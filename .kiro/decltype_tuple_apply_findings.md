# cpp17_apply_basic / cpp17_tuple_basic — root-cause diagnosis (2026-06-11)

Status: still KNOWNBUG. Investigated thoroughly; the root is NOT primarily
"decltype/invoke_result resolution" but **pack expansion of a dependent
member-alias type used as a template argument**, compounded by a crash and a
timeout in std::make_tuple's instantiation. A partial fix was implemented and
then REVERTED (correct + regression-free, but narrow — covered only one of
several code paths and greened no end-to-end test).

## What actually fails
- Both tests **time out** (EXIT=124), not a plain CONVERSION ERROR.
- The printed diagnostics ("invalid implicit conversion from '<<type:decltype>>'
  to 'signed int'" for apply; "expected type, but got expression" for tuple)
  are NON-FATAL/recovered (minimal repros that print them still reach
  VERIFICATION SUCCESSFUL, EXIT=0).
- The decltype, invoke_result_t, std::invoke and std::get primitives all work
  individually. std::apply with an EXPLICIT tuple works (recovers). The common
  blocker is **std::make_tuple**.

## Root cause (isolated)
make_tuple's signature:
  template<class... E>
  tuple<typename __decay_and_strip<E>::__type...> make_tuple(E&&...);
The return type is `Container<typename Trait<E>::member...>` — a pack expansion
whose pattern is a dependent member-alias, with the pack `E` nested INSIDE the
pattern (not the top-level name).

Minimal repro (p1):
  template<class T> struct W { using type = T; };
  template<class... E> struct Tup { Tup(E...){} };
  template<class... E> Tup<typename W<E>::type...> mk(E... e)
  { return Tup<typename W<E>::type...>(e...); }
  int main(){ auto t = mk(1, 2); }
Observed: the instantiated return type became `tag-Tup<signed_int>` (ONE
element) instead of `Tup<int,int>`.  The top-level `...` was not expanded into N
copies; the nested `E` then absorbed the whole pack, collapsing to one element.

`std::make_tuple` alone CRASHES: `to_struct_tag_type` precondition
(src/util/std_types.h:519) via
cpp_typecheckt::user_defined_conversion_sequence ->
implicit_conversion_sequence -> implicit_typecast -> typecheck_return
(type-checking make_tuple's `return tuple<...>(...)`), because the return type
is left unresolved (not a struct_tag).

## The (reverted) partial fix
In template_mapt::apply (template_map.cpp), the template-arg pack-expansion loop
(~648-760) only expands a pack-expansion argument whose TOP-LEVEL name is the
pack (`E...`). I added a general branch: when an `ambiguous`/cpp_name arg with
`ellipsis=true` references a pack NOT at top level, collect the referenced
pack(s), and for each element i expand a copy of the pattern with that element
bound (via a per-element copy of the template_mapt with the pack rebound as a
scalar type_map entry), per [temp.variadic]/4-5.

Result: this DID fix the function-template return-type path (p1's return type
became the correct `Tup<int,int>`), and was regression-free (full cpp14/17/20 -C
== baseline; cpp11 variadic/tuple/template/function/forward all pass).

## Why it was reverted (remaining gaps — this is multi-path)
1. ALIAS templates use a different path: `template<class...E> using MakeTup =
   Tup<typename W<E>::type...>;` then `MakeTup<int,double,char>::count` still
   resolved wrong (count != 3) — the alias-expansion path does not go through
   the apply() args loop the fix patched.
2. The in-body reconstruction `return Tup<typename W<E>::type...>(e...)` (a
   constructor-call EXPRESSION, double pack) still mis-resolved, so p1 overall
   still failed.
3. std::make_tuple still crashed (to_struct_tag_type) in some paths and timed
   out in others; the fix turned the make_tuple-alone case from a crash into a
   timeout (forward progress, but not green).
4. Net: no end-to-end test was greened.

## DEEPER DIAGNOSIS (2026-06-12): this is multi-BUG, not just multi-path

Re-took the effort. Re-applied the foundation fix and dug through every layer.
The foundation pack-expansion fix is correct and regression-free, but it only
covers ONE of several code paths, and there are SEPARATE independent bugs that
also block the tests. Reverted again (narrow, greens no end-to-end test).

### The independent blockers (each must be fixed)
1. Pack expansion of a nested-pack pattern `Container<typename Trait<E>::
   member...>` is implemented per-path, and only the FUNCTION-TEMPLATE SIGNATURE
   return-type path goes through template_mapt::apply's template-arg loop:
   - signature return type: FIXED by the foundation patch (verified:
     `mk(1,2)`'s instantiated return type became `tuple<int,int>`).
   - body EXPRESSION / member access (e.g. `Tup<typename W<E>::type...>::count`
     inside the body): NOT fixed — `fp.cpp` still yields count!=3.
   - alias template (`using MakeTup = Tup<typename W<E>::type...>`): NOT fixed —
     cpp_typecheck_resolve.cpp ~4475 does a manual one-to-one alias-param
     substitution that ignores the pack `...` entirely.
   - constructor-call expression (`return Tup<...>(e...)`): NOT fixed.
   These produce a spurious shorter instance (e.g. `tuple<int>`) alongside the
   correct one.
2. `decltype('a')` is `int`, not `char` (char literals are mis-typed) —
   confirmed via `std::is_same<decltype('a'),char>::value` == false.  This alone
   corrupts cpp17_tuple_basic's element types (it builds tuple from `'a'`):
   the generated tuple is `tuple<int,double,int>` instead of
   `tuple<int,double,char>`.  Independent frontend bug.
3. The inconsistent / spurious / versioned instantiations (`34_std::tag-
   _Tuple_impl<...>`, `44_std::tag-tuple<...>`, plus a spurious `tuple<int>`)
   produce a program on which **symex does not terminate**: with the foundation
   fix, type-checking now COMPLETES and CBMC reaches "Starting Bounded Model
   Checking", then hangs in symex (no VCCs generated) even with `--unwind 1`.
   The GOTO program has NO backward gotos (no loops) and only ~48 small
   functions, so the hang is an infinite CALL CHAIN: distinct "versions" of the
   same logical tuple/_Tuple_impl type look like different functions to symex,
   forming a cycle that recursion-unwinding does not bound.

### Net assessment
Completing this requires (a) a unified pack-expansion-of-nested-pattern
mechanism applied at all four substitution sites, (b) fixing char-literal typing
([lex.ccon]: an ordinary character literal has type `char` in C++), and (c)
ensuring instantiation consistency so symex's call graph is finite.  (c) is
likely a consequence of fully doing (a) (consistent types => no spurious
versions), but it is a real risk and the deepest unknown.  This is a large,
several-day undertaking in the most fragile part of the frontend
(template_mapt::apply is ~800 lines, heavily special-cased), with a symex-level
failure mode at the end.  cpp17_apply_basic / cpp17_tuple_basic stay KNOWNBUG.

### Foundation fix (correct + regression-free; preserved here for reuse)
In template_mapt::apply (template_map.cpp), in the cpp_name template-arg
expansion loop, AFTER the existing `ambiguous`+ellipsis (front-is-pack) case and
BEFORE `if(!was_pack) expanded_args.push_back(arg);`, add:

    // [temp.variadic]/4-5: pack expansion whose pattern is not the bare
    // pack (the pack is nested, e.g. `typename W<E>::type...`).
    if(!was_pack && arg.id() == "ambiguous" &&
       static_cast<const exprt &>(arg).type().id() == ID_cpp_name &&
       static_cast<const exprt &>(arg).type().get_bool(ID_ellipsis))
    {
      std::set<irep_idt> referenced_packs;
      std::function<void(const irept &)> collect = [&](const irept &n) {
        const irep_idt id = n.get(ID_identifier);
        if(!id.empty())
          for(const auto &pe : pack_args_map) {
            const std::string &key = id2string(pe.first);
            auto p = key.rfind("::");
            const std::string suffix =
              p != std::string::npos ? key.substr(p + 2) : key;
            if(suffix == id2string(id)) referenced_packs.insert(pe.first);
          }
        for(const auto &c : n.get_named_sub()) collect(c.second);
        for(const auto &c : n.get_sub()) collect(c);
      };
      collect(static_cast<const exprt &>(arg).type());
      if(!referenced_packs.empty()) {
        const std::size_t n =
          pack_args_map.at(*referenced_packs.begin()).size();
        bool consistent = true;
        for(const auto &pid : referenced_packs)
          if(pack_args_map.at(pid).size() != n) consistent = false;
        if(consistent) {
          for(std::size_t i = 0; i < n; i++) {
            template_mapt element_map = *this;
            for(const auto &pid : referenced_packs) {
              element_map.type_map[pid] = pack_args_map.at(pid)[i];
              element_map.pack_args_map.erase(pid);
              element_map.pack_size_map.erase(pid);
            }
            exprt element = static_cast<const exprt &>(arg);
            element.type().remove(ID_ellipsis);
            element_map.apply(element.type());
            expanded_args.push_back(static_cast<const irept &>(element));
          }
          was_pack = true;
        }
      }
    }

Validated regression-free (cpp14/17/20 -C == baseline; cpp11 variadic/tuple/
template/function/forward all pass).  Needs `<set>` (already included).

## Original (still-valid) summary of the earlier session follows below.


This is a substantial, multi-path piece of work, not a single localized fix:
- Unify pack-expansion of pattern-with-nested-pack across ALL paths: the
  function-template-return path (template_map::apply args loop), the alias-
  template expansion path, and the constructor-call expression path.
- Guard cpp_typecheckt::user_defined_conversion_sequence against a non-
  struct_tag source/target (the unguarded to_struct_tag_type is a robustness
  bug regardless).
- Investigate the make_tuple instantiation timeout (likely repeated/expensive
  re-instantiation once the return type is partially resolved).
Keep cpp17_apply_basic / cpp17_tuple_basic as KNOWNBUG until these land. Their
test.desc comments already point to the post-decay instantiation gap.

The decay (35719a9b06), nested-member-capture (4b31e68642) and typeid
(2813f682aa) fixes are unaffected and remain committed.

## PROGRESS (2026-06-12 session 3): foundation pack-expansion fix COMMITTED

Committed 009c1964ac: template_mapt::apply now expands a nested-pack pattern
Container<typename Trait<E>::member...> per element in template-argument lists
([temp.variadic]/4-5). Demonstrable + regression-free: new CORE test
cpp11_variadic_member_alias_pack passes; cpp14/17/20 -C == baseline (5
pre-existing), cpp11 excl libcxx 153 OK. The fix yields a single consistent
instantiation (tag-Tup<int,double,char>, no spurious/versioned tags) for the
deducible-return-type path. Also committed this session: char-literal typing
dbc08a6603 ([lex.ccon]).

STILL OPEN (make_tuple/tuple/apply remain KNOWNBUG):
1. Conversion crash (m4: tuple<int,int> t = make_tuple(1,2)): to_struct_tag_type
   precondition aborts via user_defined_conversion_sequence ->
   implicit_conversion_sequence -> implicit_typecast -> typecheck_return. All
   lexical to_struct_tag_type calls there (1477/1478/1530/1916/2031) are guarded
   and cpp_is_pod uses to_tag_type; the failing call is an INLINED helper not
   yet pinned (needs a RelWithDebInfo build; release build has no line info).
   Root: make_tuple's return type is not a clean struct_tag at typecheck_return
   (partially-resolved __decay_and_strip<...>::__type).
2. Symex timeout (cpp17_tuple_basic/apply_basic): type-checking completes, then
   symex hangs (no VCCs) even at --unwind 1 on a loop-free ~48-fn program — an
   infinite call chain from inconsistent instantiations of std::tuple's
   recursive-inheritance machinery. Deepest remaining unknown.

Other paths: the constructor-call expression path (pass1.cpp, "invalid implicit
conversion from struct Tup to struct Tup", same single type) is the SAME
conversion-machinery bug as #1, not an expansion bug. The ::member access
EXPRESSION path (fp.cpp) is a cpp_typecheck_resolve issue (routing cpp_name
exprs through apply(typet) did not help; reverted).

## DISCOVERY (2026-06-12): make_tuple is also blocked by a pre-existing
## variadic-function-template-body instantiation bug (independent of packs)

Minimal repros (no member alias, no decltype):
  conv3 (NON-variadic): template<class T> B<T> h(){ B<T> r; r.tag=7; return r; }
                        B<int> t = h<int>();           -> VERIFICATION SUCCESSFUL
  conv1 (VARIADIC):     template<class...E> Tup<E...> g(){ Tup<E...> r; ...; return r; }
                        Tup<int,double,char> t = g<int,double,char>();
                        -> "no body for callee g<...>()" AND
                           "invalid implicit conversion from struct Tup to struct Tup"
  conv4 (VARIADIC, decl-only): Tup<E...> g();  Tup<int,double> t=g<int,double>();
                        -> only "no body" (expected); the IDENTITY conversion
                           Tup<int,double> -> Tup<int,double> SUCCEEDS here.

So: a variadic function template whose BODY declares a local of the variadic
class type and returns it fails to instantiate a body; the "invalid implicit
conversion from struct Tup to struct Tup" is a downstream effect of the body's
`return r` not being type-checked/instantiated.  This is the SAME class of
issue as the earlier Part-2 ODR-use-driven member-instantiation work, and is
independent of pack expansion (it reproduces with a bare `Tup<E...>`).

std::make_tuple is `template<class...E> tuple<__decay_and_strip<E>...> make_tuple
(E&&...)` -- a variadic function template returning a variadic class by value --
so it hits THIS bug too, in addition to (a) pack expansion [now fixed], (b) the
to_struct_tag_type conversion crash on the partially-resolved return type, and
(c) the symex infinite-call-chain timeout.

Net: cpp17_apply_basic / cpp17_tuple_basic are blocked by several INDEPENDENT,
pre-existing deep bugs.  The pack-expansion conformance bug is fixed and
committed (009c1964ac); the rest is a multi-bug, multi-session effort.

## ROOT-CAUSE FOUND (2026-06-12 session 4): build() binds a pack param as a
## scalar in type_map; fixing it greens tuple_basic but regresses optional

The variadic-function-template "no body" / "invalid implicit conversion from
struct Tup to struct Tup" reduces to: in template_mapt::build(), the parameter
loop calls set(template_parameters[i], instance[i]) for EVERY position,
including the trailing PACK parameter -- binding the pack E as a SCALAR to its
FIRST element in type_map, in addition to the correct pack_args_map[E]=[all].
With E in both maps, contexts that consult type_map collapse the pack to its
first element (e.g. the temporary `Tup<E...>{}` in a function body resolves to
`Tup<int>` instead of `Tup<int,double,char>`), which then fails to convert to
the (correctly-expanded) return type.

FIX (in build(), the instance loop): only set() the NON-pack parameters; the
trailing pack is handled solely by the pack block (pack_args_map / pack_size_map,
and type_map only for the size-1 convenience case):
    const std::size_t n_non_pack =
      has_pack ? template_parameters.size()-1 : template_parameters.size();
    if(i < n_non_pack) set(template_parameters[i], *i_it);

RESULT with this fix:
  + cpp17_tuple_basic -> VERIFICATION SUCCESSFUL (0/36 failed)! The consistent
    instantiation also resolves the earlier symex non-termination.
  + conv1/conv5's "invalid implicit conversion from struct Tup to struct Tup"
    disappears.
  - REGRESSES cpp17_optional_basic + cpp17_optional_has_value: a libstdc++
    variadic trait used by optional's converting-constructor constraint
    (optional:784, _Requires<...is_constructible..., __not_<__converts_from_
    optional>...>) now yields `struct nil` -> "invalid implicit conversion from
    struct nil to __CPROVER_bool", and _Optional_payload members (_M_get,
    _M_reset) go unknown -> main elided.  So some libstdc++ trait/_Optional_
    payload instantiation RELIES on the (buggy) scalar pack binding in type_map.
  - Does NOT fix conv1's "no body" (free variadic fn template returning by
    value still gets no body even once the conversion error is gone -- a
    separate ODR-use/instantiation gap), nor apply_basic (still times out;
    make_tuple+apply adds the decltype/invoke chain), nor m4's to_struct_tag_type
    crash (explicit-target-type conversion path).

NET: the build() fix is standard-correct and greens tuple_basic, but is
net-negative (regresses 2 optional tests) until the libstdc++-trait /
_Optional_payload dependency on the scalar pack binding is fixed (the correct
fix is to make that code path consult pack_args_map / handle the pack properly
rather than read type_map[pack]).  REVERTED for now; tuple_basic stays KNOWNBUG.
The fix code is preserved above for a follow-up that also addresses the
optional dependency.

## UPDATE (2026-07-09): current root cause is "template parameter after a pack"

The pack-expansion rework (phases 0-5, committed) and the char-literal fix
resolved the earlier timeout/crash. cpp17_tuple_basic now TYPE-CHECKS and RUNS
symex; it fails only because `std::get<0>(make_tuple(1,2.0,'a')) == 1` is
violated: the trace shows `make_tuple` returns `{._M_head_impl=0, =0.0, =4}` --
the argument values are never stored. goto-functions show the tuple /
_Tuple_impl / _Head_base CONSTRUCTORS have NO bodies (only dtors, _M_head,
_M_swap are emitted), so `make_tuple`'s `return tuple(...)` initialises nothing.

Root-caused (minimal, header-free) to: **a function template whose template
parameter list has a parameter FOLLOWING a parameter pack** ([temp.param]/11),
e.g. std::_Tuple_impl's forwarding constructor
`template<class _UHead, class... _UTail, class = enable_if_t<...>>`.  Minimal
reproducer (regression/cbmc-cpp/cpp11_template_param_after_pack):

    template<class U, class... W, class X = void> int first(U u, W...) { return u; }
    first(5, 6, 7);   // g++ OK; CBMC: "found no match" / CONVERSION ERROR

Isolation: pack LAST (no trailing param) works; a NON-variadic ctor with an
extra defaulted param works; only a param AFTER a pack fails.  `sizeof...` and
forwarding are irrelevant.  Called from inside another template body, the outer
body is dropped ("no body for callee").

Mechanism (traced through cpp_typecheck_resolvet::guess_function_template_args):
1. DEDUCTION layer: after the non-empty pack is expanded, the deduced
   template-argument list is longer than the parameter list; the
   default-application loop uses a 1:1 params[i]<->args[i] mapping capped at
   params.size(), so the trailing parameter's (defaulted) argument slot is
   skipped and left ID_unassigned -> `has_unassigned()` -> deduction returns
   nil.  A pack-aware mapping (args index -> param index shifted by the pack
   width) makes the default apply and deduction SUCCEED (verified: produces a
   valid `int first(int,int,int)` instance with args [int,int,int,void]).
2. DISAMBIGUATION/INSTANTIATION layer (STILL OPEN): even with (1) fixed and a
   valid instance returned by guess, the candidate is still rejected downstream
   ("found no match"), i.e. the resolve_identifierst disambiguation /
   instantiate_template path also needs to handle the param-after-pack instance
   (whose flat #C_template_arguments has one entry per expanded pack element
   plus the trailing param).  `template_mapt::build` already binds a pack at any
   position correctly, so the remaining gap is between guess returning the
   instance and its selection/instantiation.

The (1) deduction fix alone changes the internal failure point but greens no
end-to-end test, so -- per this file's established discipline -- it was NOT
committed.  Recorded as KNOWNBUG cpp11_template_param_after_pack.  Completing
Cluster B needs layer (2) plus the remaining make_tuple/apply chain
(apply_basic still hits the decltype/invoke_result member-instantiation gap,
Part 2).

## UPDATE (2026-07-09 cont.): Layer 2 is multi-sublayer in the instantiation engine

Traced Layer 2 (the deduced param-after-pack instance still rejected after Layer 1
makes deduction succeed).  Sequence for `first(5,6,7)` with
`template<class U, class... W, class X = void> int first(U u, W...)`:
- Layer 1 (deduction, cpp_typecheck_resolve.cpp ~7036 default-arg loop): a
  pack-aware arg->param index mapping makes X's default apply; guess returns a
  valid instance whose (already-expanded) function_type is `int(int,int,int)`
  with flat #C_template_arguments = [int,int,int,void].  VERIFIED.
- resolve then RE-INSTANTIATES that template_function_instance via
  instantiate_template(template_symbol, [int,int,int,void]).
  template_mapt::build (template_map.cpp) correctly binds W={int,int}, X=void
  (pack_count = nargs - (nparams-1) = 4-2 = 2; VERIFIED via probe).
- Layer 2a (cpp_instantiate_template.cpp ~5199 free-function pack expander):
  assumed the pack is the LAST template parameter
  (`template_parameters().back().get_bool(ID_ellipsis)`) and took pack args from
  index nparams-1 to the end.  Made it pack-position-aware (find the ellipsis
  param at any index; pack args = full_template_args[pack_idx .. pack_idx +
  (total - (nparams-1))); identical when the pack is last).  VERIFIED via probe:
  it then computes packarg = {int,int} correctly.
- Layer 2b (STILL OPEN): DESPITE Layer 2a computing {int,int}, the instantiated
  symbol `first<int,int,int,void>` STILL has parameters [int,int,void] at
  disambiguate_functions (cpp_typecheck_resolve.cpp ~1810), so it is rejected as
  non-viable for (5,6,7) -> "found no match" / CONVERSION ERROR.  I.e. the final
  symbol's parameter list is produced by ANOTHER expansion/substitution path
  (or a cached earlier instantiation) that still mis-attributes the trailing
  template arg (X=void) to the pack -- Layer 2a's expander output does not reach
  the symbol.  The next probe should find which path sets the instantiated
  symbol's parameters (candidate: an earlier cached instantiation during guess's
  own disambiguate at cpp_typecheck_resolve.cpp ~1078, or template_map.apply of
  the function type) and make it pack-position-aware too.

Net: Layer 1 + Layer 2a are correct and behaviour-preserving for the common
pack-is-last case, but green no end-to-end test while Layer 2b remains, so per
this file's discipline they were REVERTED.  cpp11_template_param_after_pack stays
KNOWNBUG.  Fully supporting a template parameter after a pack requires auditing
EVERY instantiation/resolution path that currently assumes the pack is the last
template parameter (build fixed; the free-function expander is Layer 2a; Layer 2b
is a further such path) -- a multi-day effort in the most fragile frontend code,
consistent with this cluster's documented scope.

## LANDED (2026-07-09): template parameter after a pack — Layers 1, 2a, 2b, 2d fixed

Committed 5c7eef307d (src) + 58cc0bb166 (test flip to CORE).  Four coordinated,
standards-grounded fixes, each removing a "pack is the last template parameter"
assumption:
- Layer 1: deduction default-argument loop maps arg positions to template
  parameters accounting for the expanded pack width; iterates all arg slots so a
  trailing parameter's default is applied.
- Layer 2d: pack_size_map recorded BEFORE that loop so a trailing parameter's
  `sizeof...(pack)` default (e.g. an enable_if) sees the deduced count
  ([temp.variadic]/8).
- Layer 2b: guess-side per-element pack type assignment indexes the pack's
  arguments from the pack's POSITION in the template parameter list, not from
  non_pack_count (which is the pack start only when the pack is last).
- Layer 2a: the free-function parameter-pack expander in
  cpp_instantiate_template.cpp finds the pack at any position and takes its
  arguments from the correspondingly-offset run of the flat list.

Result: `first(5,6,7)` for `template<class U, class... W, class X = void>` now
resolves (direct, via a template body, as a constructor, and with an
`enable_if<sizeof...(W)==N>` trailing constraint).  cpp11_template_param_after_pack
flipped KNOWNBUG->CORE.  cbmc-cpp + cbmc pass; dog-food unchanged; the 8 jbmc
exception failures are pre-existing (confirmed on the stashed baseline, Java-only).

## STILL OPEN for cpp17_tuple_basic: recursive forwarding base-class ctor call

With the above landed, std::make_tuple still returns a tuple with uninitialised
members (get<0> reads 0) and the _Tuple_impl/_Head_base CONSTRUCTORS still have
no goto bodies.  The remaining blocker, isolated header-free: a recursive
variadic *forwarding* constructor whose member-initializer constructs its base
from the tail pack --

    template<int I, class Head, class... Tail>
    struct TI<I,Head,Tail...> : TI<I+1,Tail...>, HB<I,Head> {
      typedef TI<I+1,Tail...> Inh;
      template<class UH, class... UT, class = eif<sizeof...(UT)==sizeof...(Tail)>>
      TI(UH&& h, UT&&... t) : Inh(fwd<UT>(t)...), Base(fwd<UH>(h)) {}
    };

fails with "found no match for symbol 'Inh'" -- the recursive base-class
constructor call `Inh(fwd<UT>(t)...)` in the member-initializer list does not
resolve (a param-after-pack forwarding constructor invoked recursively over the
shrinking tail).  This is the next layer for tuple_basic; apply_basic
additionally needs the Part-2 decltype/invoke_result member-instantiation work.

## LANDED (2026-07-09): recursive forwarding base-ctor with an empty pack + param-after-pack

Committed ac809c0e1e (src) + CORE test cpp11_recursive_forwarding_tuple_ctor.
The recursive variadic forwarding constructor layer (std::_Tuple_impl shape) is
fixed: a parameter pack deduced to zero elements at the terminal recursion, with
further template parameters after it, no longer breaks deduction.  Two residual
"pack is last" assumptions in guess_function_template_args were fixed: (1) the
default-argument loop truncated trailing parameters at an empty pack's
placeholder (now erases only the placeholder and continues, tracking the shift);
(2) pack_size_map is now recorded even for an empty pack (size 0), so a trailing
`sizeof...(pack)` default (an enable_if constraint) resolves the CURRENT pack via
scope-qualified lookup instead of a stale outer same-named pack.  A faithful
header-free mini-std::tuple (recursion + forwarding + std::forward + enable_if
<sizeof...(UT)==sizeof...(Tail)> + empty-pack terminal) now stores each element
correctly.  cbmc-cpp + cbmc pass; dog-food unchanged; jbmc's 10 exception/catch
failures are pre-existing (confirmed identical on the stashed baseline).

## STILL OPEN for cpp17_tuple_basic: libstdc++ tuple's many-overload ctor selection

Real std::make_tuple STILL returns a tuple with uninitialised members and the
std::_Tuple_impl / std::_Head_base constructors STILL have no goto bodies, with
NO diagnostic emitted.  The instantiated std::tuple constructors present are the
allocator-taking overloads (allocator_arg_t variants) with an unresolved `_Alloc`
template parameter; the plain forwarding constructor make_tuple selects
(`tuple(_UElements&&...)` guarded by the _TupleConstraints SFINAE) does not get a
body.  This is a distinct, larger layer -- libstdc++ std::tuple's ~10 constructor
overloads plus the _TupleConstraints / is_constructible SFINAE and the Part-2
ODR-use-driven member-function-body instantiation -- not the recursive-forwarding
mechanism (which the faithful reproducer above now exercises correctly).
cpp17_tuple_basic / cpp17_apply_basic stay KNOWNBUG.

## CHARACTERIZED (2026-07-09): tuple ctor SFINAE layer = member alias template two-parallel-pack

Traced cpp17_tuple_basic's remaining blocker precisely.  Direct multi-element
`std::tuple<int,double,char> t(1,2.0,(char)3)` fails (single-element works): the
forwarding constructor `tuple(_UElements&&...)` is SFINAE-rejected because
`_ImplicitCtor<...>` -> `_TupleConstraints<true,_Elements...>::
__is_implicitly_constructible<_UElements...>()` evaluates to FALSE though it
should be TRUE.  `make_tuple` then has no body and the tuple ctors that DO get
instantiated are the allocator variants with an unresolved `_Alloc`.

Reduced header-free (regression/cbmc-cpp/cpp11_alias_template_parallel_pack):
the failure is a MEMBER ALIAS TEMPLATE whose body expands TWO PARALLEL PACKS --
the alias's own pack and the enclosing class's pack, exactly the
_TupleConstraints shape:

  template<class... Types> struct C {
    template<class... Us> using sums = sum_t<same_t<Us,Types>::v...>;  // parallel packs
    template<class... Us> static constexpr int chk(){ return sums<Us...>::v; }
  };
  C<int,double,char>::chk<int,double,char>()  // g++: 3; CBMC: wrong ("no match for 'v'")

The individual pieces work: inlined parallel-pack traits (not via a member alias)
evaluate correctly; a single member alias template (one pack pattern) works; only
the member-alias + two-parallel-pack combination fails.

ROOT (traced, probes): when the member alias `sums<Us...>` is resolved
(resolve_template_alias -> instantiate_template), it is reached with ZERO
template arguments -- the pack `Us...` passed as the alias's argument list is not
expanded to the concrete elements.  So the alias's own pack (`Us`) is never bound
(type_map empty, pack_args_map holds only the enclosing class pack `Types`), and
the two-parallel-pack body expansion (template_map.cpp apply -> the
nested-pack `referenced_packs` lock-step loop) collects only `Types` (the one
pack that IS in pack_args_map), leaving the alias pack reference unresolved.  So
`same_t<Us,Types>` becomes `same_t<unresolved, Types[i]>` -> mis-evaluates.

MULTI-SUB-BUG (why this is a distinct, larger layer):
  (a) the pack `Us...` supplied as a template-alias argument list is not expanded
      before the alias is instantiated (resolve_template_alias gets 0 args) --
      likely the alias is resolved during the enclosing template's ABSTRACT
      elaboration (pack unbound) and/or the pack-as-alias-arg expansion path
      does not run;
  (b) consequently the alias's own parameter pack is not bound in the map used to
      substitute its body; and
  (c) the two-parallel-pack lock-step expander only pairs packs that are BOTH in
      pack_args_map, so an unbound alias pack is left unresolved.
Fixing (a)/(b) (bind the alias's pack; expand a pack passed as an alias argument
list) should let the existing lock-step expander (c) pair both packs.  This is
the tuple-constraint layer; cpp17_tuple_basic / cpp17_apply_basic stay KNOWNBUG.
Recorded as KNOWNBUG cpp11_alias_template_parallel_pack.

## REFINED (2026-07-09 cont.): sub-bugs (a)/(b) re-diagnosed; real bug is (c)/(d)

Careful re-tracing with a CLEAN reproducer (deduced args, no explicit-args
confound) refuted the earlier (a)/(b) framing and found TWO distinct bugs:

BUG 1 (separate, real, NOT the tuple blocker): a QUALIFIED template-id naming a
STATIC member function template of a class template, WITHOUT the `template`
keyword, drops the member's explicit template args:
  `C<int>::chk<int,double,char>()`  (chk = `template<class... Us> static ...`)
resolve_scope sees the cpp_name `C<int>::chk` with NO template_args for chk (the
parser did not attach them; `qualified=1` path), so chk is instantiated
abstractly (sizeof...(Us)==wrong).  Adding `template` (`C<int>::template
chk<...>()`) fixes it; g++ does not require `template` for the non-dependent
`C<int>`.  libstdc++'s tuple uses `template` (`_TCC<_Cond>::template
__is_implicitly_constructible<...>`), so it does NOT hit this.  My earlier
"resolve_template_alias gets 0 args" finding was this confound.

BUG 2 (the tuple blocker): a MEMBER ALIAS TEMPLATE whose body is a two-parallel-
pack expansion `Trait<Types, Us>...` (class pack + the alias's own pack) fails
even with DEDUCED args and no confound (reproducers TY1/TY2, AL-unqual all FAIL;
g++ OK).  Decisive trace:
  - The alias IS instantiated with the right args (tc_nargs=3).
  - `template_mapt::build` DOES bind the alias's own pack (BUILD3:
    pack_args_map[C<...>::...::27::Us] = {int,double,char}, size 3).
  - BUT during the alias BODY substitution (template_mapt::apply of
    `all_t<is_c<Types,Us>::value...>`), the nested-pack `collect()` sees a
    pack_args_map containing ONLY the class pack `Types` -- the alias's own pack
    `::27::Us` binding is GONE.  So `collect()` finds only `Types`, the
    lock-step expander pairs one pack, and `Us` is left unresolved
    ("found no match for symbol 'value'/'v'").
So the binding built for the alias's pack is LOST between build() and the body
apply() -- a template_map lifecycle issue confined to alias instantiation (the
built pack binding does not survive to the aliased-type substitution).  This is
the real fix site (NOT "expand the pack-as-alias-arg" and NOT "bind the alias
pack" -- both already happen; the binding just doesn't reach the body apply).

STATUS: root pinned but not yet fixed (deep template_map lifecycle in
instantiate_template's alias path).  KNOWNBUG cpp11_alias_template_parallel_pack
stands; BUG 1 (static qualified template-id without `template`) is a separate
worthwhile fix.  No source change landed this turn; tree clean.

## ROOT CAUSE COMPLETE (2026-07-10): alias body expanded eagerly during class instantiation

Instrumented the transition build() -> alias-body apply() with ordered probes.
Decisive ordering for the confound-free reproducer
(`template<class... Types> struct C { template<class... Us> using ctible =
all_t<is_c<Types,Us>::value...>; ... };`):

  COLLECT_AT refpacks=[Types] packkeys=[Types(3)] packsize=[Types=3]   <-- FIRST
  AFTER_BUILD sym=C<...>::ctible<Type0> pack_args_map=[Types(3), Us(3)] <-- LATER

i.e. the alias body's parallel-pack expansion `is_c<Types,Us>::value...` runs in
`template_mapt::apply`'s nested-pack loop **BEFORE** ctible is ever instantiated
with concrete arguments -- during the enclosing class C<int,double,char>'s
instantiation.  At that point ONLY the class pack `Types` is bound (present in
both pack_args_map and pack_size_map); the alias's OWN pack `Us` is entirely
absent (unbound -- it is still a template parameter of the not-yet-instantiated
member alias template).  The expander's `collect()` therefore finds only `Types`,
drives the lock-step expansion by `Types` (n=3), and leaves every `Us` reference
unsubstituted.  This wrong, half-expanded body
(`all_t<is_c<int,Us>::value, is_c<double,Us>::value, is_c<char,Us>::value>`, with
`Us` dangling) is baked into ctible's instance and reused when ctible is later
used with concrete args -> "found no match for symbol 'value'".

This violates N5008 [temp.alias]/2: an alias template is substituted only at each
point of use with its own template arguments; C's instantiation must NOT expand a
member alias template's body pack expansion over the alias's OWN parameter pack.

FIX DIRECTION (next step): in the nested-pack expander (template_map.cpp
~1078-1140), do NOT expand a pack-expansion pattern that references a parameter
pack which is NOT bound in the current map (the alias's own, still-a-template
pack) -- leave the `...` intact so it is expanded later, at the alias's point of
use, when BOTH packs are bound.  Equivalently, when substituting a member alias
TEMPLATE's aliased type during the enclosing class's instantiation, apply only
the class arguments and preserve pack expansions over the alias's own parameters.
The detection hinges on recognising `Us` as an (unbound) parameter-pack reference
rather than a concrete name; the pattern must not be collapsed while any pack it
expands over is unbound.

## FIX ATTEMPT (2026-07-10): sound deferral needs info absent at the expander

Attempted the fix direction (defer the nested-pack expansion while the alias's
own pack is unbound).  Instrumentation established the hard constraints:

1. At the premature expansion (template_mapt::apply nested-pack loop,
   template_map.cpp ~1078), the alias's own pack `Us` is an UNMARKED bare `name`
   node (NODE probe: `node_id=name type_id=nil ell=0`) and is absent from ALL
   maps (pack_args_map / type_map / pack_size_map show only the class pack
   `Types`).  So the expander cannot self-detect that `Us` is an (unbound) pack
   -- it is indistinguishable from an ordinary name (`is_c`, `value`).  A
   heuristic "defer if the pattern contains any unbound name" over-defers and
   would regress legitimate concrete-type-in-pack patterns (e.g.
   `pair<Types, ConcreteType>...`).

2. template_mapt has NO access to cpp_typecheckt / the instantiation stack /
   scopes, so the expander cannot look `Us` up as a template-parameter pack.

3. The eager expansion happens during an ABSTRACT context (class pack bound, the
   member alias's own pack unbound) and the half-expanded body is reused; the
   concrete ctible instantiation (which DOES bind both packs -- AFTER_BUILD
   probe) does not re-expand correctly because it reuses the baked body.

SOUND FIX (requires a moderately-invasive, carefully-validated change): thread
the member alias template's OWN parameter-pack names to the substitution as
"pending/unbound packs" (e.g. add them to a new set on template_mapt, or as an
ID_unassigned sentinel that the expander treats as "pack present but unbound"),
recorded at the point the class instantiation substitutes the member alias
template's body -- so the nested-pack expander DEFERS (leaves the `...` intact)
whenever the pattern references a pending/unbound pack, and the expansion runs
only at the alias's point of use (ctible<...>), when both packs are bound
([temp.alias]/2).  The blocker for landing it this session was locating the
exact class-instantiation substitution call that reaches the member alias
template's body (it is a single recursive template_mapt::apply that does not
distinguish the alias-body boundary) and doing so without regressing the many
existing pack/alias CORE tests -- needs a dedicated, full-suite-validated pass.
Root cause is fully established; no heuristic (regression-risking) fix was landed.

## CORRECTED via MINIMIZATION (2026-07-10): TWO separate bugs, one now FIXED

Prompted by "are we using the smallest test?", bisected the 11-line `chk`/
two-arg-trait/recursive-`all_t` reproducer DOWN.  The confounding structure hid
the actual defect.  Minimization results (each row a controlled change):

- Direct explicit use `C<int,int>::ctible<int,int>::value` (no `chk`): PASSES.
- Through member fn template `chk`: FAILS.  -> not class elaboration.
- Alias uses ONLY its own pack `Us` (V1) OR only the class pack (V2): both FAIL.
  -> NOT about two parallel packs.
- Single-element pack: PASSES.  Multi-element: FAILS.  -> the >=2 case.
- Namespace-scope alias, no class, no `chk` (N5): FAILS.  -> not member alias.
- Free fn template, NO alias (N3): FAILS.  -> not the alias.
- Type-based pattern `is_1<Us>...` (P1): PASSES.  Value pattern
  `is_1<Us>::value...` (N5): FAILS.  -> the `::value` member access.
- Explicit (no pack) `all_t<is_1<int>::value, is_1<char>::value>` (D1): FAILS.
  Fixed-arity `template<bool,bool>` (E1): PASSES.  -> the VARIADIC NON-TYPE PACK.

TRUE MINIMAL (5 lines, no class/alias/member/pack-expansion):
    template<bool...> struct all_t{ static constexpr bool value=true; };
    template<class A> struct is_1{ static constexpr bool value=true; };
    all_t<is_1<int>::value, is_1<char>::value>::value;   // 2nd is_1 empty

ROOT CAUSE (BUG A, now FIXED, commit 89ae579832): in
`typecheck_template_args`, the loop consuming the EXTRA arguments matched by a
variadic parameter pack treated every `ambiguous` argument as a TYPE
(`typecheck_type`).  For a NON-type pack (`template<bool...>`) the 2nd+ argument
`is_1<T>::value` was thus resolved as a type-name inside an empty `is_1<T>`
(`NOMATCH base=value scope=is_1<char>:: ncand=0`).  The 1st argument was fine
(main loop distinguishes type vs non-type params).  Fix routes a non-type pack's
extra args through the expression path.  Validated: cbmc-cpp all pass (102
skipped), new CORE test cpp11_nontype_pack_member_value_args.  Note: the nested-
pack EXPANDER (template_map.cpp) was proven CORRECT here (it produced
`is_1<int>::value`/`is_1<char>::value` with the right substituted types) -- so
the earlier "expander/alias" hypothesis was a red herring.

REMAINING (BUG B, still KNOWNBUG cpp11_alias_template_parallel_pack): a genuine
TWO-parallel-pack MEMBER alias body `same_t<Us,Types>::v...` (Us + the class
pack) still evaluates to a WRONG (non-constant) value even after Bug A's fix
(H1 deduced and H2 explicit-with-`template` both VERIFICATION FAILED, no longer
a CONVERSION ERROR).  This is a distinct defect from Bug A.  There is also a
separate PARSER bug: `C<int,char>::ctible<int,char>::value` at namespace scope
gives "parse error before ', char > ::'".

## BUG C FIXED + BUG B CORE FIXED + BUG D ISOLATED (2026-07-10)

Bug C (parser, FIXED -> CORE, commit "parse a member template-id after a
non-dependent class-template-id"): rVarNameCore rejected
`C<int>::al<char>::value` (no `template` keyword).  Two fixes: (1) accept a
following `::` in the speculative template-arg check (a `name<...>::` is a
nested-name-specifier -> template-id), (2) mirror rName so a concrete
class-template-id qualifier is not treated as dependent ([temp.names]/5).

Bug B core (two-parallel-pack member-alias EXPANSION, FIXED, commit "defer a
member alias template's own-pack expansion"): during class instantiation the
member alias body `same_t<Us,Types>::v...` was expanded by the class pack
`Types` alone (its own pack `Us` unbound), giving `sum_t<1,0,0>`.  Fix defers a
pack expansion whose pattern references the alias's own (unbound) pack; it is
expanded at the alias's point of use with both packs bound -> `sum_t<1,1,1>`
(verified via the resolved instance tag).  No cbmc-cpp regressions.

Bug D (RESIDUAL, KNOWNBUG cpp11_alias_pack_expansion_forwarded_pack): a
pack-expansion alias `sums = sum_t<sizeof(Us)...>` instantiated with a pack
FORWARDED from an enclosing function template (`sums<Us...>::v` in `chk`) does
not fold -- `chk()` is left unconstrained.  Minimal: free fn template + namespace
alias (NO class needed).  Bisection: no-pack member alias `::v` folds; namespace
alias with EXPLICIT concrete args folds; only a pack-expansion alias body with a
FORWARDED pack fails.  This masks Bug B end-to-end (so
cpp11_alias_template_parallel_pack stays KNOWNBUG) and is the residual blocker
for std::tuple's _TupleConstraints.  NEXT: fix Bug D (fold a pack-expansion alias
instantiated with a forwarded pack), then cpp11_alias_template_parallel_pack and
(pending further layers) cpp17_tuple_basic.

## BUG D PRECISELY CHARACTERIZED (2026-07-10) -- NOT yet fixed

Re-investigated the residual "Bug D" (renamed test:
cpp11_nontype_value_pack_fn_template).  The earlier "pack-expansion alias with a
forwarded pack doesn't fold" description was imprecise (the alias and `sizeof`
were confounds).  DECISIVE finding (instrumentation): a pack expansion whose
pattern is a NON-TYPE value dependent on the pack -- `Trait<Us>::value...` -- as
the template-argument list of a template-id in a FUNCTION TEMPLATE's body is
resolved ABSTRACTLY at the function template's DEFINITION (pack unbound):
`box<sz<Us>::v...>` produces only `box<Non_Type0>` (INST_BOX probe fired once,
name `template.box<Non_Type0>`, nargs=2), and is NOT re-instantiated concretely
when `chk<char,char>` is instantiated (no concrete `box<1,1>` ever appears),
so `::n`/`::v` is unconstrained.  Controls: the TYPE-id form `box<sz<Us>...>` and
a bare pack `box<Us...>` DO re-instantiate concretely and work; only the
non-type `::value` form fails.  typecheck_template_args's expander DOES fire at
instantiation with Us(2) (TCA_SZ probe), but the concrete box is never
instantiated -- the abstract `box<Non_Type0>` baked into chk's body at definition
is reused.  This is the two-phase issue: a dependent non-type template ARGUMENT
(`sz<Us>::v`) causes the enclosing template-id to be resolved to an abstract
instance at definition instead of staying dependent (the type-argument form
stays dependent and re-instantiates).  A correct fix must keep such a template-id
dependent and re-instantiate it at the function template's point of
instantiation; this is a substantial two-phase-name-lookup change and was NOT
attempted this session to avoid a rushed fix in that machinery.  It is the shape
of std::tuple's `__and_<is_X<_Types,_UTypes>...>::value` and the residual blocker
for cpp11_alias_template_parallel_pack / cpp17_tuple_basic.

## BUG D FIXED -> CORE (2026-07-10): sizeof...(P) for a non-type parameter pack

Re-minimized Bug D to its true root, which was NOT "forwarded pack doesn't fold"
but a `sizeof...` bug: `box<1,1>::n == 2` (with `n = sizeof...(Vs)` and
`template<unsigned... Vs>`) failed DIRECTLY -- no chk/alias/forwarding -- and was
wrong for every arity (box<1>, box<1,2,3>).  A TYPE parameter pack worked.
DECISIVE (probe): the parser reads `sizeof...(P)` via rTypeName (-> ID_type_arg,
counted by the `#sizeof_pack` path) for a type pack, but a NON-type pack does not
parse as a type-id, so its name was read via rName and stored as an OPERAND; the
operand is type-checked to a stray constant BEFORE typecheck_expr_sizeof's
pack-count path runs (probe: at typecheck_expr_sizeof, op0_id=constant).  Fix
(parse.cpp): store the non-type pack's name in ID_type_arg too, so both forms
take the pack-counting path.  Verified for arities 1/2/3, type packs unaffected,
full cbmc-cpp green; flipped cpp11_nontype_value_pack_fn_template to CORE.

RESIDUAL for the two-parallel-pack (cpp11_alias_template_parallel_pack, still
KNOWNBUG): a recursive non-type-pack trait value (`sum_t<...>::v`, sum_t recurses
over its pack) instantiated with a FORWARDED pack in a function template
(`sum_t<sizeof(Us)...>::v` inside chk) still does not fold -- distinct from both
the sizeof... count bug and the alias-expansion bug.  Next target.

## TWO-PARALLEL-PACK MEMBER ALIAS WORKS FOR TYPE PACKS -> CORE (2026-07-10)

Investigating the "next target" (the two-parallel-pack residual) showed the
earlier `sum_t<...::v...>` reproducer was an UNFAITHFUL non-type-pack proxy.  The
tuple's actual _TupleConstraints shape uses a TYPE parameter pack
(`__and_<is_X<_Types,_UTypes>...>::value`, `template<class...> __and_`).  Tested
the faithful TYPE-pack pattern -- `and_<is_same<Us,Types>...>::value` via a
member alias inside `chk` -- and it now PASSES (matched -> true, mismatched ->
false; direct, 2- and 3-element, all correct).  So after the prior fixes
(operator combined-candidate-set, param-after-pack, recursive-forwarding-ctor,
non-type-parameter-pack arguments, member-alias own-pack deferral, sizeof... of
a non-type pack, qualified-nested-template-id parser), the two-parallel-pack
member alias -- the real tuple constraint machinery -- is correct.

Rewrote cpp11_alias_template_parallel_pack to the faithful TYPE-pack shape and
flipped it to CORE (non-vacuous: matched vs mismatched).

RESIDUAL NON-TYPE-PACK DEFECTS (separate from the tuple; new KNOWNBUGs):
  - cpp11_nontype_pack_recursive_two_elem: a recursive NON-type pack trait
    (`sum_t<H,T...>{v=H+sum_t<T...>::v}`) fails to type-check for EXACTLY TWO
    elements (0/1/3/4 work; TYPE analogue works; non-recursive partial-spec
    deduction works).
  - cpp11_nontype_pack_sizeof_expr_forwarded: a `sizeof(Us)...` (sizeof
    unary-expression) pack expansion forwarded through a function template
    expands to the wrong arity (a `Trait<Us>::v...` member-value pattern
    forwarded the same way is correct -- cpp11_nontype_value_pack_fn_template).

NOTE: cpp20_concepts_ordering_gcc14 is a documented Clang-20-preprocessor-
sensitive test; a stale/incremental binary can make it transiently fail.  A
clean rebuild passes it 5/5 both with and without the sizeof... fix (which is not
on its code path), confirming no regression.

## DERIVED-TO-BASE DEDUCTION (non-template derived) FIXED -> CORE (2026-07-10)

Chasing cpp17_tuple_basic's `get<0>` wrong value, minimized the get<> mechanism
(recursive `_Tuple_impl` inheritance + `__get_helper<I>` deducing
`_Tuple_impl<I,Head,Tail...>` from the derived tuple).  Two false leads: (a) a
name collision when the reproducer's outer pack shared the deducer's pack name
`T` (artifact), (b) it works for a template-instance derived class with distinct
names.  REAL bug found: derived-to-base deduction from a NON-template derived
class (`struct D : impl<0,int,char>`) aborted at guess_template_args' "argument
not instantiated from a template" guard before the derived-to-base dispatch ran.
Fixed by walking the argument class's bases for a specialization of the deduced
template and retrying (handles a non-empty trailing pack; deeper index selects a
deeper base).  cpp11_derived_to_base_variadic_deduction flipped to CORE; full
cbmc-cpp green.

REAL TUPLE RESIDUAL (cpp17_tuple_basic, still KNOWNBUG): narrowed to element
count -- a 2-element tuple is fine end-to-end, but a 3-element tuple fails:
`make_tuple(a,b,c)` gives a wrong `get<0>` and manual `tuple<A,B,C> t(a,b,c)`
fails constructor resolution ("no match for symbol 'tuple'").  A hand-written
faithful minimal tuple works at all arities, so the residual is in libstdc++'s
tuple CONSTRUCTOR machinery at >=3 elements (the _TupleConstraints-guarded
variadic constructor / element storage), NOT get<> deduction.  Next: cvise the
preprocessed 3-element case.

## CVISE ISOLATION OF cpp17_tuple_basic 3-ELEMENT BUG (2026-07-10)

Preprocessed the failing `make_tuple(1,2.0,3.0f)`+`get<0>` case (g++ -E, 4277
lines) and ran cvise with a robustness-guarded interestingness (reduced program
must (1) compile under g++ and run under valgrind with the assertion HOLDING --
no uninitialised-value use -- so the program is well-defined and any cbmc failure
is a genuine bug; (2) still mention `tuple`/`get`; (3) make cbmc report the
assertion FAILURE).  First pass over-reduced to a degenerate uninitialised-int
proxy; the valgrind guard fixed that.

Result: a 78-line header-free reproducer that g++ runs correctly (get<0>==1) but
cbmc rejects with "found no match for symbol 'tuple'".  HOWEVER a faithfulness
check showed it is a cvise ARTIFACT, NOT the real tuple bug:
  - Completing the cvise-reduced (incomplete) `_TupleConstraints` with a trivial
    `static constexpr bool __is_implicitly_constructible = true;` makes cbmc
    SUCCEED.  The real libstdc++ `_TupleConstraints` is complete, so this
    reduction's "bug" (cbmc rejecting a SFINAE ctor whose constraint names an
    INCOMPLETE type) is not the real defect.
  - clang++ REJECTS the reduced code (missing `template` keyword on a dependent
    member template; non-type partial-spec argument depending on a partial-spec
    parameter): it is only g++-extension-accepted, i.e. ill-formed, so cbmc
    rejecting it is not clearly a bug.  (Not committed as a test.)

Oracle limitation: dual g++/clang validation cannot force faithfulness here --
clang cannot compile g++-preprocessed libstdc++ (g++ builtins like
`__remove_reference`), and `g++ -pedantic-errors` does not flag the artifact.

NEXT (build-up instead of reduce-down): start from a hand-written faithful tuple
that cbmc handles CORRECTLY (recursive `_Tuple_impl`, plain variadic ctor,
`get<>` via `__get_helper` base deduction -- verified working) and add the real
libstdc++ features one at a time -- (a) `make_tuple` element decay
(`__decay_and_strip`), (b) `get`'s `tuple_element`/`_Nth_type` return type,
(c) the COMPLETE `_TupleConstraints`-based SFINAE constructor with the
two-parallel-pack `is_constructible<_Elements,_UElements>...` -- until the
3-element case regresses, isolating the true interaction.  (Individually, each of
these has a passing test: two-parallel-pack -> cpp11_alias_template_parallel_pack
CORE; derived-to-base get<> -> cpp11_derived_to_base_variadic_deduction CORE.)

## FAITHFUL REPRODUCER RECOVERED by repairing the cvise artifact (2026-07-10)

The 78-line cvise output was ill-formed (clang rejects: incomplete
`_TupleConstraints` in a nested-name-specifier, missing `template` keyword, bad
partial spec).  But its STRUCTURE was the right tuple shape.  Repairing it into
standard-conforming C++ -- completing `_TupleConstraints` with a REAL
two-parallel-pack constexpr constraint `and_<is_ctible<_Elements,_UElements>::
value...>::value`, a proper `_Head_base`, and derived-to-base `get` -- yields a
clang-clean, g++/clang-run-correct reproducer that STILL fails in CBMC.  So the
tuple bug is faithful, not an artifact.

Minimal essence (committed as cpp17_tuple_get_two_pack_ctor_3elem, header-free):
a `tuple<_Elements...>` variadic converting constructor guarded by
`enable_if_t_<_TupleConstraints<_Elements...>::ic<_UElements...>()>` (a
two-parallel-pack fold over the class pack and the constructor's own pack) fails
to evaluate at >= 3 elements -> "found no match for symbol 'tuple'" -> get<0>
reads nondet.  TWO elements work; a plain unconstrained variadic constructor
works.  So the trigger is specifically the TWO-parallel-pack constexpr constraint
in a variadic constructor's SFINAE default template argument at >= 3 elements
(distinct from the standalone two-parallel-pack alias, which is CORE, and from
sizeof.../derived-to-base, both fixed).  Also reproduces via direct
`tuple<int,double,float> t(1,2.0,3.0f)` construction.  NEXT: fix that constraint
evaluation.  Note: the *inlined* constraint form (constraint directly in the
ctor's enable_if, no `_TupleConstraints` wrapper) fails even at 2 elements -- a
broader related variant.

## FIX ATTEMPT: tuple ctor bug traced to recursive non-type pack (2026-07-10)

cpp17_tuple_get_two_pack_ctor_3elem root-cause chain (all steps confirmed):
  1. `tuple` ctor SFINAE `enable_if_t_<_TupleConstraints<E...>::ic<U...>()>`.
     Direct test: `_TupleConstraints<int,double,float>::ic<int,double,float>()`
     evaluates FALSE/nondet at 3 elements (should be true) -> ctor discarded
     -> "no match for symbol 'tuple'".  So the bug is the CONSTRAINT eval, not
     the enable_if/ctor context.
  2. `ic()` returns `and_<is_ctible<E,U>::value...>::value`.  The two-parallel-
     pack expansion COUNT is correct (cnt<is_ctible<E,U>::value...>::n == 3);
     `and_<true,true,true>` DIRECT works.  So the args and count are right.
  3. The failure is in `and_`'s recursion over the member-value bool pack: it
     routes through `and_<...>` with a forwarded 2-element non-type pack, which
     is the SAME bug as cpp11_nontype_pack_recursive_two_elem.
  4. Minimal root (cpp11_nontype_pack_recursive_two_elem): `sum_t<2,3>::v`
     (recursive non-type pack, EXACTLY 2 elements, at top level) fails.  CBMC
     error: instantiating sum_t<2,3>, body `2 + sum_t<T...>::v` -> the
     `sum_t<T...>::v` (deduced non-type pack T={3}) is left UNRESOLVED
     (`2 + <<expr:cpp_name>>` -> "implicit arithmetic conversion not permitted").
  5. CONTEXT-SENSITIVE: `sum_t<2,3>::v` at TOP LEVEL (in main's constexpr
     assertion) fails, but the SAME `sum_t<2,3>` instantiated RECURSIVELY (as a
     sub-step of `sum_t<1,2,3>`) succeeds.  So it is not a pure substitution bug
     -- it is that substituting the deduced non-type pack T into the recursive
     template-id `sum_t<T...>` in the member initializer, and triggering the
     recursive instantiation `sum_t<3>`, is dropped in the top-level
     constant-expression instantiation context but works when reached from an
     enclosing (non-constexpr-eval) instantiation.

FIX SCOPE: this is a non-type-parameter-pack substitution / recursive-
instantiation-triggering defect in the top-level constant-expression context
(instantiate_template + template_map.apply of a `Template<pack...>::member`
value in a constexpr member initializer).  It is the fundamental root of the
tuple constructor failure; fixing cpp11_nontype_pack_recursive_two_elem should
cascade.  Deferred as a dedicated pass: the top-level-vs-nested context
sensitivity indicates an instantiation-ordering interaction that needs careful,
regression-guarded work rather than a rushed substitution change.  Minimal
KNOWNBUG already exists: cpp11_nontype_pack_recursive_two_elem.

## CONSTRAINT-EVAL ROOT: two-part non-type-pack defect (2026-07-10, attempt)

Located the root of cpp11_nontype_pack_recursive_two_elem / the tuple ctor
constraint failure precisely (probes):
  ROOT PART 1 (storage gap): template_mapt has NO storage for a NON-type
  parameter pack's element VALUES.  `pack_args_map` (types) is filled in
  template_mapt::build only for args with `id()==ID_type`; a non-type pack's
  args are constants (`instance[j].id()==ID_constant`), so pack_args_map stays
  empty (only pack_size_map gets the count).  Hence a pack expansion `sum_t<T
  ...>` over a non-type pack cannot be expanded -- the expander in apply() finds
  the pack in neither map and leaves `sum_t<T...>::v` unsubstituted, producing
  `2 + <<expr:cpp_name>>` -> "implicit arithmetic conversion not permitted".
  Also: the bare-pack ellipsis for a NON-type pack sits on the `ambiguous` ARG
  node (`arg.get_bool(ID_ellipsis)`), not on `arg.type()` as for a type pack.

  ROOT PART 2 (recursive-instantiation trigger): even after substituting
  `sum_t<T...>` -> `sum_t<3>` (a prototype fix did this, verified), `sum_t<3>` is
  NOT instantiated during `sum_t<2,3>`'s member-initializer typecheck, so
  `sum_t<3>::v` stays unresolved.  `sum_t<3>::v` resolves fine at top level, so
  this is a nested-instantiation-triggering gap in the member-initializer
  (constant-expression) context -- related to the Part-2 ODR-use member
  instantiation findings.

FIX ATTEMPT (reverted): added `pack_expr_mapt pack_expr_map` (irep_idt ->
vector<exprt>) to template_mapt, populated non-type pack values in build(),
broadened the bare-pack expander branch to accept the arg-level ellipsis and to
expand a non-type pack from pack_expr_map.  This correctly expanded `sum_t<T...>`
-> `sum_t<3>` (probe PEXP) BUT (a) did not green the target -- ROOT PART 2 still
leaves `sum_t<3>::v` unresolved -- and (b) regressed libcxx_comma_in_template_arg
(the broadened arg-level-ellipsis condition mis-fires for a comma-in-template-arg
case).  Reverted rather than ship a partial, regressing change.

COMPLETE FIX needs, together: (1) a precise non-type-bare-pack detection (not the
blanket arg-level-ellipsis broadening that regressed libcxx_comma_in_template_
arg), (2) pack_expr_map storage + expander expansion for non-type pack VALUES,
and (3) triggering the recursive instantiation of the substituted nested value
(`sum_t<3>`) in the member-initializer context.  Sizeable, regression-guarded.

## "PART 2" IS NOT SEPARATE; CANONICAL ROOT = non-type pack forwarding collapse (2026-07-10)

Concrete recursive member initializers work in CBMC (`rec<N>::v`, `rec2<2,3>::v`
all SUCCESSFUL), so the earlier "Part 2 recursive-instantiation" was an artifact
of the reverted prototype substituting a MALFORMED / inconsistent non-type arg,
not a separate defect.

CANONICAL ROOT (new KNOWNBUG cpp11_nontype_pack_forward_collapse): forwarding a
NON-type parameter pack `T...` into another template-argument list
(`fwd<2,3>` -> `cnt<T...>::n`) collapses to ONE element for >= 2 elements
(`fwd<2,3>::n` == 1, not 2).  One element works (single-element pack also gets a
scalar type_map entry); a direct `cnt<2,3>::n` works.  So `pack_args_map`
(type-only) has no non-type pack VALUES (build() collects only ID_type args), and
the expander cannot expand `T...`.  MASKED when both comparison sides collapse
equally (`__is_same(dummy<Pred...>, dummy<((void)Pred,true)...>)`, hence
libcxx_comma_in_template_arg passes) but EXPOSED by count/value reads.  This is
the shared root of cpp11_nontype_pack_recursive_two_elem,
cpp11_nontype_pack_sizeof_expr_forwarded, cpp17_tuple_get_two_pack_ctor_3elem.

COMPLETE FIX (why the earlier bare-only prototype regressed): must store non-type
pack values (pack_expr_map) AND expand them CONSISTENTLY in BOTH expander
branches -- the bare `T...` branch and the nested-pattern `Trait<T>...` branch
(binding the per-element value in the nested element_map).  Fixing only the bare
branch makes the two sides of `__is_same(dummy<Pred...>, dummy<((void)Pred,
true)...>)` disagree (one 2-element, one collapsed) and regresses
libcxx_comma_in_template_arg.

## COMPLETE-FIX ATTEMPT 2 (both branches) -- still insufficient + regressing (2026-07-10)

Re-implemented with pack_expr_map + build population + BOTH expander branches
(bare non-type `T...` gated on the name being a recorded non-type pack; nested
`Trait<T>...` collect()/size/consistency extended to pack_expr_map and per-element
expr_map binding).  Result: still did NOT green fwd<2,3>/sum_t<2,3>, and STILL
regressed libcxx_comma_in_template_arg.  Reverted.

So the model "store non-type pack values + expand in both apply() branches" is
NOT sufficient.  Additional interacting moving parts (to investigate in a
dedicated pass):
  - The PRIMARY-template non-type pack (fwd<2,3>'s `T`) may not be recorded in
    pack_expr_map by build() the same way the partial-spec pack is (the primary
    pack-binding path differs), so the bare branch never fired for it.
  - The value ARG FORM produced by the expander for a non-type element must
    match what downstream cpp_name resolution / typecheck_template_args expects
    (the reverted prototype's `sum_t<3>` was not resolved).
  - libcxx_comma_in_template_arg's `dummy<Pred...>` (bare) vs
    `dummy<((void)Pred,true)...>` (nested) must expand CONSISTENTLY; the nested
    branch also flows through typecheck_template_args' OWN pack expander
    (cpp_typecheck_template.cpp ~1770, type-only), which likewise needs the
    non-type path, or the two sides still disagree.
Net: the non-type-pack expansion is handled in at least THREE places
(template_mapt::build, template_mapt::apply's two branches, and
typecheck_template_args' expander); a correct fix must make ALL consistently
non-type-aware with a matching arg form.  Sizeable, dedicated, regression-guarded.

## FIX LANDED: non-type parameter pack expansion (2026-07-10)

ROOT (confirmed by code review of template_mapt::build): a non-type parameter
pack was SCALAR-BOUND to its first argument in expr_map -- exactly the collapse
build() already avoids for TYPE packs via the `is_type_pack` gate + pack_args_map.
So `Foo<T...>` over a non-type pack collapsed to one element for >=2 elements;
one element worked via the single-element convenience.  "Part 2" (recursive
instantiation) was disproven: concrete recursion works; the earlier symptom was a
malformed arg from a partial prototype.

FIX (committed b88cdb0686), mirroring type-pack handling in ALL expansion sites:
1. template_mapt::pack_expr_map (value analogue of pack_args_map); build()'s gate
   now skips the scalar bind for ANY pack and records non-type values + a
   single-element expr_map convenience.
2. template_mapt::apply expands a bare non-type pack `T...` from pack_expr_map in
   the type-context expander AND the value-context subst_params.
3. typecheck_template_args' pack expander made non-type-aware (gated on
   pack_expr_map) and extended to VALUE patterns: libc++'s comma idiom
   `((void)Pred,true)...` is expanded per element (each pack ref substituted by
   its i-th value) and folded to the comma's right operand ([expr.comma]).  This
   was the sole thing making the bare side and the comma side disagree.

RESULT: whole cbmc-cpp suite green, no regressions (libcxx_comma_in_template_arg
previously passed only via mutual collapse of both __is_same sides).  Flipped to
CORE: cpp11_nontype_pack_forward_collapse, cpp11_nontype_pack_sizeof_expr_
forwarded.

STILL KNOWNBUG (separate issue): a recursive PARTIAL SPECIALIZATION naming itself
over the trailing non-type pack (`sum_t<H,T...>::v = H + sum_t<T...>::v`,
`and_<H,T...>`) at two elements -- the substituted `sum_t<3>` is expanded but not
recursively instantiated/resolved.  Tracks cpp11_nontype_pack_recursive_two_elem
and cpp17_tuple_get_two_pack_ctor_3elem.

## RECURSIVE NON-TYPE-PACK PARTIAL SPEC (cpp11_nontype_pack_recursive_two_elem) — precise root (2026-07-10)

Still KNOWNBUG (deep, pre-existing).  Precisely localized:
- `sum_t<2,3>` (partial spec `sum_t<H,T...>`, H=2, T={3}) instantiates; its member
  initializer references `sum_t<T...>` = `sum_t<3>` (trailing 1-element pack ->
  0-element trailing pack).
- Elaborating `sum_t<3>` runs partial-specialization matching, which RE-TYPE-CHECKS
  the specialization PATTERN `<H,T...>` via `typecheck_template_args` under an
  SFINAE context.  For the empty deduced trailing pack the call throws (`throw 0`
  from a NESTED substitution, not the arg-count/missing-type checks at
  cpp_typecheck_template.cpp:1971/2013/2227/2354 — those do NOT fire).  Candidate
  skipped -> `sum_t<3>` falls back to the INCOMPLETE PRIMARY (forward decl, no
  members).
- At top level a later member-access completion recovers `sum_t<3>`; inside
  `sum_t<2,3>`'s member initializer (SFINAE + suppress_elaborate) the failure is
  final -> `sum_t<3>::v` stays an unresolved cpp_name.
- DECISIVE: pre-instantiating any `cc<single>` first makes `cc<2,3>` succeed; the
  TYPE-pack analogue (`ct<H,class...T>`) folds correctly at all arities — so the
  reference path exists and the defect is specific to the NON-type empty-trailing-
  pack pattern re-type-check.

Committed this session: `build_unassigned` now clears pack_expr_map like
pack_args_map/pack_size_map (db7ed04545) — correct consistency fix, no regression,
but not sufficient (the SFINAE-fail is in the pattern re-type-check, not the leak).

NEXT: make the partial-spec pattern re-type-check tolerate an empty deduced
trailing NON-type pack (mirror the type-pack path) so `sum_t<3>` matches its
specialization on first elaboration.  Then cpp11_nontype_pack_recursive_two_elem
and (cascading) cpp17_tuple_get_two_pack_ctor_3elem should green.

## FIX LANDED: recursive partial spec with empty deduced trailing pack (2026-07-10)

Root (localized last turn, fixed now): selecting a recursive class-template
partial specialization re-type-checks its pattern args ([temp.class.spec.match]).
For `sum_t<H,T...>` naming itself over the trailing pack, the nested `sum_t<3>`
(where `T` deduces EMPTY) re-type-checked the pattern `<H,T...>` with the
non-type `T...` still present; a non-type pack expansion over an empty pack is
evaluated as an unassigned scalar and throws, so the candidate was rejected as
SFINAE and `sum_t<3>` fell back to the incomplete primary -> `sum_t<3>::v`
unresolved inside `sum_t<2,3>` (failed at exactly two elements).

FIX (dc02e33326): before the pattern re-type-check, trim trailing pack-expansion
arguments corresponding to an empty deduced pack (pattern has more args than the
actual), per [temp.arg.explicit]/4 note 1 + [temp.variadic]/4 (empty pack
expansion -> zero elements).  Local to specialization matching; mirrors the
existing trailing-empty-pack trim of the type-checked result.  A first attempt
that registered the empty pack as pack_size_map=0 and broadened the
typecheck_template_args pack-expander gate regressed 5 tuple/variadic CORE tests
(CONVERSION ERROR) and was reverted in favour of this local trim.

RESULT: whole cbmc-cpp suite green, no regressions.  Flipped to CORE:
cpp11_nontype_pack_recursive_two_elem, cpp17_tuple_get_two_pack_ctor_3elem (the
faithful 3-element std::tuple SFINAE-ctor reduction).

STILL KNOWNBUG: cpp17_tuple_basic (get<0> still FAILURE -- a further layer in the
full libstdc++ tuple) and cpp17_apply_basic (separate `decltype` front-end
limitation: body left incomplete).

## cpp17_tuple_basic ROOT ISOLATED: forwarding-ref variadic ctor + recursive base (2026-07-10)

cpp17_tuple_basic (make_tuple(1,2.0,'a'); get<0> reads wrong value) root, isolated
to a header-free reproducer (cpp11_fwdref_pack_ctor_recursive_base, KNOWNBUG):

A variadic constructor with a FORWARDING-REFERENCE parameter pack
`tuple(_U&&... __e) : _Tuple_impl<0,_E...>(static_cast<_U&&>(__e)...)`, forwarding
each element through a RECURSIVE base (`_Tuple_impl<_Idx,_Head,_Tail...> :
_Tuple_impl<_Idx+1,_Tail...>`), stores the WRONG (nondeterministic) element values
when the deduced pack `_U` has DISTINCT types (`tuple<int,double>`).  Narrowing:
  - by-VALUE variadic ctor pack (`_U... __e`) forwarding to the same recursive
    base: CORRECT (cpp17_tuple_get_two_pack_ctor_3elem, CORE).
  - forwarding-ref pack into a NON-recursive fixed-arity target
    (`two(static_cast<U&&>(u)...)`): CORRECT.
  - forwarding-ref pack with SAME types (`tuple<int,int>`): CORRECT.
  - forwarding-ref pack + recursive base + DISTINCT types: WRONG / nondeterministic
    (members left uninitialized); an inlined-head variant even CRASHES with
    `cpp_typecheck_code.cpp:1782 typecheck_member_initializer: "at least one
    parameter"`.
So the defect is the member-initializer processing of a forwarding-reference
variadic constructor pack expansion `static_cast<_U&&>(__e)...` forwarded into a
recursive base's own forwarding-reference ctor (the ctor body/member-init is not
correctly instantiated/bound for heterogeneous deduced `_U`).  Real libstdc++
uses a non-variadic two-element tuple specialization, so make_tuple hits this
only at 3+ elements.

cpp17_apply_basic is a SEPARATE issue (std::apply's decltype/invoke_result return
type stays `<<type:decltype>>` via the lazy ODR-use member-instantiation path;
tracked in the apply test.desc / part2 findings), not the forwarding-ref bug.

NEXT: fix member-initializer instantiation for a forwarding-reference variadic
constructor pack expansion forwarding into a recursive base with heterogeneous
deduced element types.

## REFINEMENT: recursion not needed -- member-initializer forwarding-ref pack (2026-07-10)

Simplified below the recursive tuple: even a NON-recursive
  struct wrap : base2 { template<class...U> wrap(U&&...u) : base2(static_cast<U&&>(u)...) {} };
  wrap w(11, 22.0);   // base2(int,double)
stores WRONG (nondeterministic) values for distinct types.  But:
  - named forwarding-ref params `wrap(A&&x,B&&y):base2(static_cast<A&&>(x),static_cast<B&&>(y))` : CORRECT
  - the SAME pattern in a FUNCTION body `two mk(U&&...u){ return two(static_cast<U&&>(u)...); }` : CORRECT
So the gap is specifically the MEMBER-INITIALIZER pack expansion of a
forwarding-reference pack `Base(static_cast<U&&>(u)...)`: the function-call
argument-pack expander (template_mapt::expand_call_argument_packs) handles the
function-body form, but the constructor member-initializer path does not expand
the two-parallel-pack pattern (`U` type pack + `u` function-parameter pack) in
lock-step, leaving the base's members uninitialized (nondeterministic).  FIX
SITE: member-initializer instantiation (cpp_typecheck_code.cpp typecheck_member_
initializer + the ctor-body substitution), mirroring expand_call_argument_packs.

## FIX LANDED: forwarding-ref ctor member-init parallel type-pack (2026-07-10)

Fixed the forwarding-reference variadic constructor member-initializer bug
(cpp11_fwdref_pack_ctor_recursive_base, now CORE).  Root: typecheck_compound_
declarator replicates the function parameter pack `base -> base$k` in the member-
initializer argument list but did NOT substitute a PARALLEL template type pack in
the same pattern.  For `Base(static_cast<_U&&>(u)...)` / `Base(std::forward<_U>(u)
...)` the `_U` was left as an unsubstituted cpp_name -> static_cast type mismatch
-> uninitialised (nondeterministic) base subobject for heterogeneous types.
Fix (2a7ff8e603): when replicating each member-init argument for element k, also
replace a bare cpp_name naming a template type pack by that pack's k-th element
type (from template_map.pack_args_map), in lock-step with the value-pack rename
([temp.variadic]/4-5).  Verified: minimal wrap, static_cast and forward<U> forms,
and the KNOWNBUG all green; whole cbmc-cpp suite green, no regressions.

STILL KNOWNBUG: cpp17_tuple_basic (real libstdc++ make_tuple(1,2.0,'a'); get<0>
still FAILURE) has a FURTHER layer beyond the forwarding-ref member-init (the
hand-written forwarding-ref reproducer and the forward<U> form now work, so the
residual is elsewhere in the real _Tuple_impl chain -- to re-characterize).
cpp17_apply_basic remains the separate decltype/invoke_result ODR-use issue.

## NEXT-LAYER REDUCTION STATUS (2026-07-10)

Forwarding-ref layer: DONE (cpp11_fwdref_pack_ctor_recursive_base, CORE; fix
2a7ff8e603).

cpp17_tuple_basic NEXT layer: NOT yet isolated to a FAITHFUL minimal test.
- cvise on the real preprocessed tuple repeatedly produces DEGENERATE artifacts
  that trigger cbmc "no match"/FAILURE via non-faithful constructs, not the real
  cause: (a) a bare uninitialised int (UB; g++ passes by luck) -- fixed by a
  valgrind guard; (b) `std::forward<T>(x)` reduced to a no-call `forward<T>...`
  function-id pack; (c) a variadic ctor passing the WHOLE pack `u...` to a
  differently-sized recursive base `base<T...>(u...)` (arity-odd; g++ accepts the
  variadic ctor) -> "no match for symbol 'base'".  The faithful tail-forwarding
  form (real tuple) PASSES, so these are reduction artifacts.
- Incremental FAITHFUL reproductions ALL PASS, ruling out (individually and in
  combination): forwarding references; real is_constructible/is_convertible
  (__is_constructible/__is_convertible builtins); _TupleConstraints<bool,...> with
  __is_implicitly/explicitly_constructible; _ImplicitCtor/_ExplicitCtor enable_if;
  both `const E&...` and `U&&...` (implicit+explicit) ctors + overload resolution;
  __valid_args<U...>() constexpr member-function-template SFINAE default arg;
  _Head_base with the __empty_not_final bool parameter; __decay_and_strip in
  make_tuple.
- REMAINING candidates to try next: the tuple<> / tuple<_T1,_T2> partial
  specializations coexisting with the primary (overload interference); the
  allocator_arg ctors; _UseOtherCtor / the tuple-from-tuple converting ctors;
  or a specific COMBINATION.  A stronger cvise interestingness that both runs
  clean under valgrind AND keeps get<0>==1 meaningful still over-reduces via the
  forward-no-call path; a `forward`-preserving guard (require the reduced program
  to still call a 1-arg forwarding function) may be needed.

cpp17_apply_basic: not yet reduced; separate decltype/invoke_result ODR-use layer.

## cpp17_apply_basic CORE LAYER ISOLATED (2026-07-10)

Header-free KNOWNBUG cpp11_decltype_return_nontype_pack_call isolates apply's
core: a function template with a TRAILING RETURN TYPE that is a `decltype` of a
CALL containing a pack expansion -- `template<int...I> auto impl(seq<I...>) ->
decltype(add(I...))` -- is not resolved by CBMC ("found no match for symbol
'impl'").  This is exactly libstdc++ std::apply's `__apply_impl` return type
`decltype(__invoke(f, get<_Idx>(t)...))`.  Narrowing: a fixed-argument decltype
call (`decltype(add(1,2))`) and plain `auto`/`decltype(auto)` forwarding returns
all work; the defect is specific to a decltype return type over a pack-expansion
call.  Distinct from the std::tuple construction layer -- fixing it should
unblock cpp17_apply_basic and may help other invoke_result/decltype-return uses.

## apply core: non-type pack call-arg expansion -- root localized (2026-07-10)

cpp11_decltype_return_nontype_pack_call ("no match for symbol 'impl'"): the true
defect is `add(I...)` -- a NON-type parameter pack expanded as CALL ARGUMENTS.
Even `return add(I...)` (no decltype) fails; a fixed-arg `decltype(add(1,2))` and
plain auto/decltype(auto) returns work.  Narrowing (ECAP probe on the decltype
path): expand_call_argument_packs IS reached, but the deduced pack `I` has
pack_args_map[I] EMPTY (n=0) and pack_expr_map EMPTY -- only pack_size_map[I]=2
is set (so sizeof...(I) works).  So the non-type pack records its SIZE but not
its element VALUES; `add(I...)` has nothing to expand.

Done: expand_call_argument_packs now consumes pack_expr_map for a non-type call-
arg pack (building block, committed, no regression) -- inert until values exist.

REMAINING (root): the deduced/bound non-type parameter pack's element VALUES must
be populated into pack_expr_map (guess_template_args / build), not just its size.
TWO call-arg-expansion paths also need it: (1) decltype operands via
expand_call_argument_packs (now pack_expr_map-aware); (2) FUNCTION BODY calls
(`return add(I...)`) which bypass expand_call_argument_packs and go through the
method-body / compound expansion -- that path needs the same non-type handling.

## apply/deduced non-type pack: progress + remaining (2026-07-10)

Fixed EXPLICIT non-type pack call arguments (cpp11_nontype_pack_call_args_explicit
CORE): expand_call_argument_packs now consumes pack_expr_map (96756b56c6) and a
function-template body runs it when a non-type pack is present (dc8c6e0668).
Fixed non-type pack VALUE DEDUCTION from a class-template-id arg
(guess_template_args now fills pack_expr_map, this commit).

REMAINING for the DEDUCED case (cpp11_decltype_return_nontype_pack_call /
cpp17_apply_basic, which deduce the pack from seq/index_sequence): build_template_
args (template_map.cpp) emits ONE argument per template PARAMETER -- a single
placeholder for a pack (lookup_expr(I) = the first value) -- and the
post-deduction "[temp.variadic]/5 expand pack parameter to N copies" step in
guess_function_template_args expands only TYPE packs to full arity, not a
NON-type pack's values.  So the deduced `<1,2>` collapses to `<1>` and impl is
mis-instantiated ("no match").  NEXT: emit a non-type pack's full element values
(from pack_expr_map) when expanding the guessed template arguments to full arity.

## RESOLVED: deduced decltype-return non-type pack call (2026-07-10)

cpp11_decltype_return_nontype_pack_call flipped KNOWNBUG -> CORE.  Full chain of
fixes for a NON-type parameter pack expanded as call arguments:
  1. expand_call_argument_packs consumes pack_expr_map (96756b56c6)
  2. function-template body runs it when a non-type pack is present (dc8c6e0668)
  3. guess_template_args records the deduced pack's VALUES in pack_expr_map,
     NOT an empty pack_args_map that would shadow them (7835827b75 + ad1bef578b)
  4. guessed template args expand a non-type pack to full arity (8a5a0fe9cd)
New CORE tests: cpp11_nontype_pack_call_args_explicit,
cpp11_nontype_pack_call_args_deduced, cpp11_decltype_return_nontype_pack_call.

## NEXT LAYER (new KNOWNBUG): auto / decltype(auto) return deduction over a pack call
cpp11_auto_return_deduce_pack_call (KNOWNBUG, header-free, faithful: g++ runs
r==3, clang++ accepts).  A DEDUCED return type (`auto`/`decltype(auto)`) whose
body returns a pack-expansion call leaves the body incomplete ("could not fully
type-check 'main'").  Trailing `-> decltype(add(I...))` works; the deduced
return type does not.  This is the remaining cpp17_apply_basic layer (std::apply
and __apply_impl both return decltype(auto)).  NEXT: make return-type deduction
(auto/decltype(auto)) expand a pack-expansion call in the return statement --
likely the same expand_call_argument_packs applied when deducing the return type
from the return expression (cpp_typecheck_method_bodies / the auto-deduction
path), mirroring the trailing-decltype handling.

## RESOLVED: auto / decltype(auto) return deduction over a pack call (2026-07-13)

cpp11_auto_return_deduce_pack_call flipped KNOWNBUG -> CORE.  Root cause: a
DEDUCED return type (auto/decltype(auto)) is type-checked EAGERLY by
convert_function (so the return type is known at the call site), bypassing the
deferred method-body drain that runs expand_call_argument_packs.  The eager path
type-checked the unexpanded `add(I...)`, failing both the return-type deduction
and the body type-check -> the instance's return type stayed unresolved ("found
no match").  Fix (71d0250ce7): expand the body's call-argument packs from the
instance's pack_expr_map at the start of convert_function, gated on
has_auto(type) && non-empty pack_expr_map (idempotent, deferred path untouched).
Covers explicit and deduced packs, auto and decltype(auto).

REMAINING for cpp17_apply_basic: a further layer -- the real libstdc++ path
routes std::apply through std::__invoke / std::get with decltype(auto) via the
lazy, ODR-use-driven member-function instantiation, whose body is not
instantiated at the decltype site ("invalid implicit conversion from
'<<type:decltype>>' to 'signed int'").  Tracked as Part 2 (part2_findings.md);
not reproduced by the header-free minimal shapes (all now pass).

## MINIMAL REPRODUCER for the cpp17_apply_basic blocker (2026-07-13)

cpp17_nested_decltype_auto_pack_call (KNOWNBUG, header-free, faithful: g++ runs
r==3, clang++ accepts).  Exact error of apply_basic ("invalid implicit
conversion from '<<type:decltype>>' to 'signed int'").

Minimal shape:
  template <class... A> decltype(auto) invoke(A... a){ return add(a...); }
  template <int... V>   decltype(auto) apply_impl(seq<V...>){ return invoke(V...); }
  apply_impl(seq<1,2>{})   // -> invoke(1,2) -> add(1,2) == 3

Bisected trigger -- ALL THREE required:
  (1) OUTER return type DEDUCED (auto/decltype(auto)); a trailing
      `-> decltype(invoke(V...))` instead gives "no match for apply_impl".
  (2) INNER callee a TEMPLATE with a deduced return type; a concrete
      (non-template) decltype(auto) invoke works.
  (3) pack size > 1; a single-element pack (seq<7>) works.
Single-level deduced return over a pack call to a KNOWN function already works
(cpp11_auto_return_deduce_pack_call, CORE).

Root (hypothesis, to confirm next): when the outer apply_impl's deduced return
type is computed (eagerly, my convert_function fix expands invoke(V...) ->
invoke(1,2)), deducing its type requires the INNER invoke(1,2)'s deduced return
type.  For a >1-element pack the inner instance's decltype(auto) is not resolved
in that nested return-type-deduction context, so apply_impl's return stays
`<<type:decltype>>`.  Likely fix locus: nested deduced-return instantiation
during return-type deduction (convert_function auto path / the resolver's
return-type computation), ensuring the inner deduced-return callee instance's
return type is deduced before it is used as the outer return expression's type.

## RESOLVED: nested decltype(auto) pack-call chain (2026-07-13)

cpp17_nested_decltype_auto_pack_call flipped KNOWNBUG -> CORE (65172066c9).
Root cause bisected precisely: the eager auto/decltype(auto) convert_function
pack expansion (71d0250ce7) may run on a NESTED deduced-return callee's body
while the ENCLOSING instantiation's template_map is still active.  At the inner
convert_function's ENTRY the body was already correctly expanded
(`add(a$0, a$1)`), but expand_call_argument_packs' value-parameter branch
(driven by pack_size_map) re-expanded that function-parameter pack against the
OUTER pack's size, corrupting it to `add(a$0, a$0)`; the callee's return type
then never resolved.  Fix: only_nontype mode -> the eager path expands ONLY the
non-type call-argument pack (pack_expr_map), leaving value/function-parameter
pack expansions to instantiation/the drain.

REMAINING for cpp17_apply_basic: STILL fails with the same error string, so the
real libstdc++ path has a FURTHER factor beyond this minimal shape (forwarding
references + real std::__invoke / std::get<Idx> over the real std::tuple, and
the lazy ODR-use-driven member instantiation of part2_findings.md).  The minimal
nested-chain layer is now closed; apply_basic needs re-narrowing on top of this.

## MINIMAL REPRODUCER #2 for cpp17_apply_basic (2026-07-13): alias-template pack deduction

After the nested-decltype(auto) fix, apply_basic still fails.  Built up from the
now-passing nested chain toward the real libstdc++ std::apply and bisected the
NEXT layer to: a NON-type parameter pack deduced THROUGH an ALIAS TEMPLATE with a
fixed leading argument.

New KNOWNBUG cpp17_alias_template_nontype_pack_deduce (header-free, faithful:
g++ runs r==3, clang++ accepts):
  template <class T, T... I> struct iseq {};
  template <__SIZE_TYPE__... I> using idxseq = iseq<__SIZE_TYPE__, I...>;
  template <__SIZE_TYPE__... J> int apply_impl(idxseq<J...>){ return add(J...); }
  apply_impl(idxseq<1,2>{})   // "found no match for symbol 'apply_impl'"
This is exactly std::index_sequence (= integer_sequence<size_t, _Idx...>) as
used by std::apply's __apply_impl parameter.

Bisection facts:
  * Deducing DIRECTLY from iseq<SIZE, J...> (no alias) WORKS (V3/S2/T1).
  * A hand-written alias with a PLAIN builtin (unsigned long) deduces only when
    the deducing function's pack name is spelled identically to the alias's own
    pack parameter (W1 pass, W2 fail) -- an accidental name-based match.
  * The real std::index_sequence fails REGARDLESS of the pack name (X1/X2) and
    with __SIZE_TYPE__/size_t the alias fails even for hand versions (U2/V1).
  * A recursive make_index_sequence-style metafunction at depth>=2 is a SEPARATE
    bug (K1), but libstdc++ uses the __integer_pack builtin, not recursion, so
    it is NOT on the apply path.
Likely fix locus: alias-template substitution during deduction -- the aliased
type pattern (iseq<SIZE, _aliasparam...>) must be re-expressed in terms of the
deducing function's pack before matching, rather than matched by the alias's own
parameter name (cpp_typecheck_resolve.cpp guess_template_args alias branch +
resolve_template_alias).

## RESOLVED (unqualified) + REMAINING (qualified) alias-template pack deduction (2026-07-13)

FIXED: cpp17_alias_template_nontype_pack_deduce KNOWNBUG -> CORE (0c5197b110 +
d61448546c).  Deducing a pack through an UNqualified alias template
(`template <SIZE... I> using idxseq = iseq<SIZE, I...>;` then `f(idxseq<J...>)`)
failed because guess_template_args' alias-substitution matched the alias
parameter by ID_C_base_name, which is EMPTY for a non-type parameter (a symbol
whose name is only the suffix of its scoped identifier `template::N::I`).  Fix:
derive the alias parameter base name robustly (C_base_name, else base_name, else
identifier suffix).  Covers non-type and type packs, differing pack names.

REMAINING: cpp17_qualified_alias_pack_deduce (KNOWNBUG, committed) -- deducing
through a QUALIFIED alias (`N::idxseq<J...>` / std::index_sequence), the exact
apply_basic shape.  The alias-expansion branch is gated on `!is_qualified()` (an
anti-recursion guard for the libstdc++ regex member-alias shape).  ATTEMPTED and
REVERTED: (a) qualified lookup via resolve_scope + QUALIFIED lookup did NOT find
the alias (still "no match"); (b) replacing the guard with a recursion set keyed
on the alias symbol id REGRESSED cpp11_alias_template_deduction -- the symbol-id
guard is too blunt: it cannot distinguish the infinite regex self-loop (alias A
re-expands to A with the SAME args) from legitimate finite nested re-expansion of
the same alias with DIFFERENT args.  NEXT: (1) get the qualified alias lookup
working (resolve_scope returned empty here -- investigate the correct scope
lookup for a qualified template-id during deduction); (2) distinguish the regex
self-loop by comparing the expansion to the input (same alias + same args =
loop) rather than by symbol id alone.

## RESOLVED: qualified alias-template pack deduction (2026-07-13)

cpp17_qualified_alias_pack_deduce flipped KNOWNBUG -> CORE (8658ea5356).  Also
greens deduction from the REAL std::index_sequence.  Root cause: guess_template_
args expanded aliases only for UNqualified template-ids (the base-name recursive
lookup found the wrong symbol for a qualified name and looped -- the libstdc++
regex member-alias shape).  Fix: resolve a qualified alias template-id via
resolve_scope + QUALIFIED lookup; proper qualified lookup resolves the alias's
own expansion target to the CLASS TEMPLATE (not back to the member alias) so it
terminates without the restriction.  KEY: resolve_scope MOVES the current scope,
so an inner cpp_save_scopet restores it before the substitution + recursive
deduction, which must resolve the enclosing function template's pack in its OWN
scope (omitting this restore both left the target failing AND regressed
cpp11_alias_template_deduction).

REMAINING for cpp17_apply_basic: STILL fails ("invalid implicit conversion from
'<<type:decltype>>' to 'signed int'") -- a further layer beyond index_sequence
deduction (the real std::__invoke / std::get<Idx> over std::tuple + decltype(auto)
chain, and the lazy ODR-use member instantiation of part2_findings.md).  Needs a
fresh re-narrowing on top of this fix.

## MINIMAL REPRODUCER #3 for cpp17_apply_basic (2026-07-13): __integer_pack builtin

After the qualified-alias fix, apply_basic still fails.  Bisected the next layer:
literal std::index_sequence deduction and getv<I>(t)... expansion now WORK
(Y2), but std::make_index_sequence<N> (Y1) fails because CBMC's C++ front-end
does not support the GCC `__integer_pack(N)` builtin ("symbol '__integer_pack'
is unknown").  libstdc++ (GCC branch) implements make_integer_sequence as
`integer_sequence<T, __integer_pack(N)...>`.

New KNOWNBUG cpp17_integer_pack_builtin (header-free, GCC-specific -- Clang uses
__make_integer_seq so rejects; g++ runs r==1):
  template <class T, T N> using mkseq = iseq<T, __integer_pack(N)...>;
  sum_impl(mkseq<unsigned long,2>{})   // "symbol '__integer_pack' is unknown"

In apply_basic the __integer_pack error is swallowed during deep decltype/SFINAE
resolution and surfaces as the unresolved `<<type:decltype>>` return type of
std::apply.  Fix locus: recognise the `__integer_pack(N)` builtin in the C++
front-end (ansi-c/cpp builtin handling) and expand it to the pack 0..N-1 in a
pack-expansion context (also support Clang's __make_integer_seq for portability).

## PARTIAL: __integer_pack builtin (2026-07-13)

FIXED direct form: cpp17_integer_pack_builtin KNOWNBUG -> CORE (b2ae70aa08 +
1b6584da31).  typecheck_template_args now detects a pack-expansion template
argument `__integer_pack(N)...` (a call to __integer_pack with a constant count)
and expands it to non-type args 0..N-1 of the argument's type, before the
per-argument type-check.  Covers direct and nested-alias forms.

REMAINING (cast form = real make_index_sequence): cpp17_integer_pack_cast_arg
(KNOWNBUG).  libstdc++ writes `integer_sequence<T, __integer_pack(T(N))...>`
(with the `T(N)` cast).  With the cast, `__integer_pack(T(N))...` is resolved
EAGERLY during the alias body substitution and never reaches
typecheck_template_args (verified: my expansion pass's probe never fires for the
cast case, while it does for the direct case).  So the real std::make_index_sequence
still fails, and cpp17_apply_basic remains blocked on it.  NEXT: expand
__integer_pack where the alias body is substituted / eagerly resolved (the path
that turns `__integer_pack(size_t(2))...` into a resolve of the unknown name),
mirroring the typecheck_template_args expansion; evaluate the (now concrete) cast
argument to the count.

## RESOLVED: __integer_pack cast argument / real make_index_sequence (2026-07-13)

cpp17_integer_pack_cast_arg flipped KNOWNBUG -> CORE (36d58f52e8).  libstdc++
writes make_integer_sequence as `integer_sequence<T, __integer_pack(T(N))...>`;
the `T(N)` cast triggers the vexing parse so the pack-expansion arg is stored as
an `ambiguous` function type (`code` returning __integer_pack, parameter `T N`).
typecheck_template_args now recognises BOTH the plain-call shape (direct) AND
this ambiguous/function-type shape (count = parameter name N, element type =
parameter type T).  Real std::make_index_sequence deduction now works.

REMAINING for cpp17_apply_basic: STILL "invalid implicit conversion from
'<<type:decltype>>' to 'signed int'" at std::apply -- the make_index_sequence
layer is now closed, so the residual is the decltype(auto) chain through the real
std::__invoke / std::get<Idx> over std::tuple (and the lazy ODR-use member
instantiation of part2_findings.md).  Needs a fresh re-narrowing on top of these
fixes.

## MINIMAL REPRODUCER #4 for cpp17_apply_basic (2026-07-13): decltype(auto) over std::get pack

After the __integer_pack fixes, make_index_sequence works; apply_basic still
fails.  Bisected the next layer: a decltype(auto) function whose body expands a
pack of REAL std::get calls, `return add(std::get<I>(t)...)` (std::apply's
__apply_impl -> std::__invoke(f, std::get<_Idx>(t)...)).

New KNOWNBUG cpp17_decltype_auto_get_pack (uses <tuple>; header-free replication
does NOT reproduce -- I/J with hand gets returning references / decltype(auto) /
via a trait all PASS, so the real std::get overload set is essential).  cbmc:
"could not fully type-check 'main'" (in apply_basic: unresolved
`<<type:decltype>>` return type of std::apply).  Tuple by reference, so
independent of the value-copy bug below.  g++ runs r==3.

SEPARATE deeper layer (NOT on apply's forwarding-ref path, but real): a
std::tuple passed BY VALUE to a template function then read by std::get yields
GARBAGE (M: `impl(T t){ return std::get<0>(t); }` -> VERIFICATION FAILED; by
REFERENCE N works).  This is cpp17_tuple_basic territory (tuple copy / get in
template context).

NEXT for apply: make decltype(auto) return deduction resolve a pack expansion of
the real std::get (its overloaded return type per element) -- likely in the
eager auto-return convert_function path + std::get overload resolution during
that deduction.

## RESOLVED: decltype(auto) over std::get pack (2026-07-13)

cpp17_decltype_auto_get_pack flipped KNOWNBUG -> CORE (a850a27e97).  Root cause
(via backtrace): resolving `std::get<I>(t)` (I = substituted non-type pack
element, a CONSTANT) also considers the by-TYPE `std::get<T>` overloads;
matching the constant against the TYPE parameter hit typecheck_type's
"unexpected cpp type: constant" HARD error, aborting the whole overload
resolution (including the viable by-index overload) -> return type never
deduced.  Fix: extend the existing template_arg_kind_mismatch machinery
(apply_template_args candidate loop) to a VALUE in type position, in BOTH the
ID_type and ID_ambiguous branches of typecheck_template_args ([temp.arg]/2 +
[temp.deduct]/8: kind mismatch removes just the candidate).  NOTE: the arg came
through the AMBIGUOUS branch; guarding only ID_type was not enough.

cpp17_apply_basic: MAJOR PROGRESS -- std::apply and __apply_impl now INSTANTIATE
(instantiation trace visible); residual error is still "invalid implicit
conversion from '<<type:decltype>>'" one level deeper (std::__invoke's
decltype(auto) / INVOKE machinery).  Needs one more re-narrowing on top of this
fix (likely the last layer).
