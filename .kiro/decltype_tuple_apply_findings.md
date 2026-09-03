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

## MINIMAL REPRODUCER #5 for cpp17_apply_basic (2026-07-13): variable-template pack partial spec

After the kind-mismatch fix, the hand-written __apply_impl chain (verbatim body,
real std::__invoke + std::get + forwarding) PASSES; even a full my_apply replica
with tuple_size<>::value PASSES.  The residual real-std::apply failure bisects to
std::tuple_size_v -- and further to a header-free root:

New KNOWNBUG cpp14_variable_template_pack_partial_spec: a VARIABLE TEMPLATE
partial specialization deducing a PACK collapses the pack to ONE element:
  template <class T>    constexpr unsigned long tsize_v            = 99;
  template <class... E> constexpr unsigned long tsize_v<tup<E...>>  = sizeof...(E);
  tsize_v<tup<int,int>>  == 1 under CBMC (g++/clang: 2; ==1 asserts SUCCESS).
Exactly libstdc++'s tuple_size_v<tuple<_Types...>>; std::apply sizes _Indices
with it, so the index sequence gets the wrong arity and the inner __invoke's
decltype(auto) fails to resolve ("<<type:decltype>>" residual).

Facts: class-template analogue (tsize<tup<E...>>::value) works; non-pack
variable-template partial spec (sz_v<wrap<T>>) works; failure is independent of
dependent context (plain main-level use collapses too).  Fix locus: variable
templates are likely lowered through the same machinery as class-template
static members / template symbols -- find where a variable-template partial
spec's pack is deduced (probably reusing the class partial-spec matcher) and why
the pack binding records only one element (compare the recursive_two_elem fix
dc02e33326 and the pack_expr_map deduction fixes).

## RESOLVED: variable-template pack partial spec (2026-07-13)

cpp14_variable_template_pack_partial_spec flipped KNOWNBUG -> CORE (a4442157d0).
Root cause: the variable-template partial-spec matcher in instantiate_template
instantiated the best match with build_template_args' single-placeholder-per-pack
args, collapsing the deduced pack to one element (tsize_v<tup<int,int>> == 1).
Fix: expand a deduced pack (pack_args_map / pack_expr_map) to full arity before
instantiating, mirroring disambiguate_template_classes.  Real std::tuple_size_v
now evaluates correctly (test covers it).

cpp17_apply_basic: STILL fails with the same "<<type:decltype>>" error --
tuple_size_v was a real defect on its path but not the last one.  Next
re-narrowing: with tuple_size_v fixed, re-run the wrapper-replica bisection
(the earlier F case "local using + ::value" ALSO failed with a DIFFERENT error,
"invalid implicit conversion from 'signed int' to '<<type:decltype>>'" -- the
reverse direction!  That suggests a residual in the local `using Ind = ...`
alias inside a decltype(auto) function).  Also re-check E (noexcept(...) spec).

## MINIMAL REPRODUCER #6 for cpp17_apply_basic (2026-07-13): local alias in decltype(auto) body

After the tuple_size_v fix, all my_apply replicas that pass make_index_sequence
INLINE pass; the residual bisects to the LOCAL `using` alias in std::apply's body
(`using _Indices = ...; return __apply_impl(..., _Indices{})`).

New KNOWNBUG cpp14_local_alias_decltype_auto_pack (header-free):
  template <int... I> decltype(auto) inner(seq<I...>){ return add(I...); }
  template <class T>  decltype(auto) outer(T){ using Ind = seq<0,1>; return inner(Ind{}); }
  outer(0) -> outer's return type NOT deduced ("invalid implicit conversion from
  'signed int' to '<<type:decltype>>'"), and here it even reaches goto-conversion
  which ABORTS (convert_return invariant, EXIT=134).  INLINE `inner(seq<0,1>{})`
  (no alias, R2) works; dependent alias (R3) also fails.  g++ runs r==1.

Root hypothesis: the eager return-type deduction (convert_function auto path)
typechecks ONLY the return expression, so a preceding local `using`-alias
declaration in the body is not in scope -> `Ind` unresolved -> `inner(Ind{})`
type unknown -> outer's decltype unresolved.  NEXT: make the return-type
deduction see the body's local declarations that precede the return (process the
body up to the return, or resolve local aliases first), OR defer more robustly.
Note the convert_return abort on an unresolved decltype return type is itself a
robustness bug worth hardening.

## *** cpp17_apply_basic GREEN (2026-07-13) ***

cpp17_apply_basic flipped KNOWNBUG -> CORE: std::apply(add, make_tuple(1,2)) over
real libstdc++ <tuple> now VERIFICATION SUCCESSFUL.

Final layer: cpp14_local_alias_decltype_auto_pack (KNOWNBUG -> CORE, 2b22a7284d).
typecheck_return deduced a return type without conversion only for plain `auto`
(ID_auto); a `decltype(auto)` return (ID_decltype + #auto) fell through and tried
to convert the return value to the unresolved `<<type:decltype>>` (and aborted
goto conversion) whenever deduction had been deferred -- which happens when the
return expression cannot be typed in isolation, e.g. std::apply's body-local
`using _Indices = ...`.  Fix: handle decltype(auto) in the same placeholder
branch (deduce without conversion; reference for a parenthesized lvalue).

Full chain that greened std::apply (all committed, each with a CORE test):
  1. non-type pack call args, explicit (expand_call_argument_packs pack_expr_map;
     method-body expansion)
  2. non-type pack call args, deduced (guess_template_args records pack values;
     guessed-args full-arity; no empty pack_args_map shadow)
  3. auto/decltype(auto) return over a pack call (eager convert_function body
     expansion)
  4. nested decltype(auto) chain (only_nontype expansion, no stale-map corruption)
  5. pack deduction through alias templates, unqualified (base-name derivation)
     and qualified (resolve_scope + QUALIFIED lookup, scope restore)
  6. __integer_pack builtin, direct and cast (make_index_sequence)
  7. tuple_size_v variable-template pack partial spec (full-arity expansion)
  8. constant in type position = template-arg kind mismatch (by-index vs by-type
     std::get overloads)
  9. decltype(auto) return with a body-local using alias (typecheck_return)

## cpp17_tuple_basic root (2026-07-13): call-pack in braced/aggregate initializer

std::make_tuple<int,int,int> (arity >= 3) is left WITHOUT a body -> nondet tuple
-> std::get reads garbage (arity 2 works).  Root, header-free
(cpp11_call_pack_in_braced_init): a variadic function-template body that expands
a pack of CALLS inside a BRACED initializer (`return box2{fwd(e)...}`) mis-expands
it -- the pack `e` inside `fwd(e)...` is substituted to `e$0, e$1` as args of a
SINGLE fwd(...) call (keeping the `...`) instead of replicating `fwd(e)` per
element into `fwd(e$0), fwd(e$1)`.  The malformed body fails convert_function
(caught in the method-body drain, which make_nils the body -> "no body for
callee").  A call-pack in a function-CALL arg list (`sum(fwd(e)...)`) IS handled
(expand_call_argument_packs / method-body expand lambda), and a braced init
without a call (`box2{e...}`) works.

FIX LOCUS: extend the call-pack expansion to braced/aggregate-initializer
(ID_initializer_list) elements, so `fwd(e)...` inside `{...}` is replicated per
element like it is inside a function-call argument list.  The pack members
arrive already renamed (e$0,e$1) inside a single call retaining the ellipsis, so
either (a) fix the instantiation-time substitution to leave `fwd(e)...` for the
method-body expand lambda to replicate (as happens for call args), or (b) teach
the expand lambda / expand_call_argument_packs to replicate a `...` child whose
body carries the full expanded member set {base$0..base$N-1}, distributing one
member per copy.  Non-trivial; well-scoped follow-up.

## PARTIAL: braced-init call-pack fixed; tuple_basic root is deeper (2026-07-13)

FIXED + CORE: cpp11_call_pack_in_braced_init (5106ff335e + 455a1e0e23).  The
instantiate-time body pack expander (expand_pack in instantiate_template) now
handles a pack expansion inside a BRACED/aggregate initializer
(ID_initializer_list), mirroring the function-call argument branch.  Previously
`box{fwd(e)...}` mis-expanded to a single `fwd(e$0,e$1)` and the body was dropped.

BUT this was NOT cpp17_tuple_basic's root: real std::make_tuple uses a CONSTRUCTOR
call `tuple<__decay_and_strip<E>::__type...>(std::forward<E>(a)...)`, not a braced
aggregate init.  cpp17_tuple_basic STILL FAILS (make_tuple<int,int,int> at arity
>= 3 has no body -> nondet tuple -> get reads garbage; arity 2 works).

Extensive header-free replication FAILS to reproduce the real root -- ALL pass:
  * paren ctor-call `box3(fwd(e)...)` (P1)
  * variadic-ctor class `vt<E...>(fwd(e)...)` (P2)
  * return-type decay pack `vt<decay<E>::type...>(fwd(e)...)` (Q1)
So the defect is specific to libstdc++'s real recursive _Tuple_impl / _Head_base
forwarding CONSTRUCTOR at arity >= 3.  Earlier goto dumps showed many tuple ctor
overloads instantiated with UNASSIGNED template params (_UElements, _Alloc) --
i.e. the arity-3 forwarding-ctor overload resolution / SFINAE
(_TupleConstraints, _Implicit/_ExplicitCtor, enable_if) selects/instantiates the
wrong (bodyless) ctor.  NEXT: trace which tuple<int,int,int> ctor make_tuple's
body calls and why its body is not instantiated at arity 3 (deep tuple-ctor SFINAE
area; a substantial standalone task).

## Cluster A (deferred/ODR-use member-body instantiation) — reproduction assessment (2026-07-13)

Cluster A = "no body for callee" for a member of a lazily-completed class-template
instance (cpp20_map_basic: _Rb_tree::operator[]; cpp11_map_insert:
_M_emplace_hint_unique; and cpp17_tuple_basic's arity-3 ctor is a cousin).

Attempted minimal reproduction, TWO ways, both unproductive:
  * Hand construction (A1-A6, member fns, member fn templates, static members,
    address-of, recursive node classes, base-class member calls) -- ALL work
    (no "no body").  The gap needs the real libstdc++ lazy-completion path.
  * cvise on preprocessed <map>:
      - weak oracle (g++ -fsyntax-only + cbmc "no body") -> DEGENERATE 7-line
        result: a `struct map { void operator[](int); };` with the definition
        REMOVED (declared-not-defined => trivially "no body", not the bug).
      - faithful oracle (g++ COMPILE+LINK+RUN exit 0 + cbmc "no body") -> cannot
        reduce below ~4471 lines: std::map genuinely needs the whole
        type_traits / stl_tree / allocator machinery to link+run, so cvise
        can't strip it.  No small faithful reproducer emerges.

Conclusion: cluster A is the Part-2 architectural gap (part2_findings.md): a
class-template instance completed by lazy substitution has its inline member
bodies registered with nil value (never sourced+substituted from the primary
template) -> "no body".  It is NOT reducible to a small header-free test and the
fix is substantial (source inline member bodies on lazy completion / drive such
instances through instantiate_template's full flow; medium-high risk, must not
over-instantiate SFINAE branches).  Recommend a dedicated session with the full
cbmc-cpp + goto-cc-cbmc baseline, not a quick KNOWNBUG->CORE flip.

## Cluster B (exception semantics) — analysis (2026-07-13)

Two KNOWNBUGs, both already minimal + header-free (only a local
`__CPROVER_assert` decl); no cvise needed.

### cpp11_throw_rethrow_nested  (root cause CONFIRMED in lowered goto)
`throw;` inside an outer handler must rethrow the exception the *dynamically
enclosing* handler is handling (N5008 [except.throw]/8, [except.handle]/1).
Bug: src/goto-programs/remove_cpp_exceptions.cpp tracks the exception being
handled in a SINGLE pair of globals `__CPROVER_cpp_current_exception{,_type}`,
not a stack.  prepare_handler() at handler entry does
  current_exc = inflight; inflight = clear;
and set_inflight_exception() for a bare `throw;` does
  inflight = current_exc;
Verified in --show-goto-functions for the test:
  * outer `catch(E&outer)` entry: current_exc := inflight (=E(1))
  * inner `catch(E&inner)` entry: current_exc := inflight (=E(2))  <-- OVERWRITES
    E(1); nothing restores it on inner-handler exit
  * outer `throw;`: inflight := current_exc  == E(2)  (WRONG; must be E(1))
So assertion 2 (`e.c==1`) FAILS.

Naive fix REJECTED (provably wrong): "save old current_exc at handler entry,
restore at the catch-var DEAD."  goto-conversion emits `DEAD <catch_var>` on the
rethrow path IMMEDIATELY BEFORE the trailing `throw;` read (verified: outer's
`DEAD main::1::1::2::outer` precedes `inflight := current_exc` by one
instruction).  Restoring at that DEAD would overwrite the value the handler's
own rethrow is about to read.  Normal-exit DEAD and rethrow-path DEAD are not
locally distinguishable (inflight is still null at both).

Correct fix (cross-phase, medium complexity, NOT a quick flip):
per-handler current-exception storage keyed by lexical nesting, so nested
handlers cannot clobber the enclosing handler's slot and NO exit-restore is
needed:
  1. front-end: maintain a handler stack in cpp_typecheckt; in
     typecheck_try_catch push the catch-var symbol (or a synthesized id for
     catch(...)) around typecheck_code(catch_block); when typechecking a bare
     `throw;` (ID_throw side-effect with no operand, cpp_typecheck_expr.cpp
     ~5777) tag it `#rethrow_handler = <enclosing handler id>`.
  2. verify the tag survives goto_convert onto the THROW instruction (may need
     goto_convert to preserve the attribute -- UNVERIFIED, a real risk).
  3. remove_cpp_exceptions: give each handler its own slot pair keyed by that
     id; prepare_handler writes inflight into the handler's slot; the rethrow
     reads the slot named by its `#rethrow_handler`.  Fall back to the single
     global for untagged/catch(...) cases.
  (A LIFO current-exception stack is the alternative, but its pop placement runs
  into the same DEAD-before-rethrow ordering problem.)
  Both still leave a recursive/looping same-handler reuse limitation, which is
  pre-existing.

### cpp11_throw_dtor_unwinding_outer_scope  (separate, deeper)
N5008 [except.ctor]/1-3: every automatic object whose scope is exited during
unwinding must be destroyed.  Here B is thrown in f() (no enclosing try in f),
an inner try catches only A, so B propagates to an outer catch(B&); object `g`
in the outer try's scope (before the inner try) must be destroyed during
unwinding.  Bug: goto-conversion destructor-unwinding only unwinds locals up to
the innermost enclosing try at the *throw point* (here f()'s own locals), not
outer scopes exited because the exception fails to match an inner handler, so
`g`'s dtor never runs.  This is a goto-convert unwinding-scope issue, distinct
from the remove_cpp_exceptions current-exception bug.

Conclusion: cluster B is genuine exception-lowering work, not a
minimal-reproducer/quick-flip.  Reproducers are already minimal + header-free;
root causes are pinned; recommend a dedicated session for the per-handler
current-exception storage (with goto_convert attribute-survival verified) and,
separately, the outer-scope unwinding fix.

## Cluster B rethrow_nested — FIXED (2026-07-13, commits c7f78e877b + bdce7e00cf)

Implemented the per-handler current-exception slot design (no exit-restore, so
the DEAD-before-rethrow pitfall is avoided entirely):
  * cpp_typecheck_code.cpp: static tag_rethrow_handler() tags each bare `throw;`
    (throw side-effect, empty operands, untagged) lexically inside a handler
    with the handler's catch-var id; inner handlers typechecked first => each
    rethrow attributed to its innermost enclosing handler.  Attr "#rethrow_handler".
  * goto_convert_side_effect.cpp: carries "#rethrow_handler" onto the THROW's
    side_effect_expr_throwt (op0) so remove_cpp_exceptions can read it.
  * remove_cpp_exceptions.cpp: handler_slots (catch-var id -> (ptr,type) globals
    __CPROVER_cpp_handler_exception${N}); prepare_handler (bound case) writes its
    slot AND the shared current_exc on entry; the rethrow reads its tagged slot
    if present, else the shared globals.  Dynamic rethrows (in a callee, or in a
    catch(...) with no catch var) stay on the shared globals -> unchanged.
Verified: cpp11_throw_rethrow_nested assertion 2 now SUCCESS; added
cpp11_throw_rethrow_inner_handler (inner rethrow => E(2)); both CORE and pass.
g++ + clang++ agree on outer=>E1, inner=>E2, sibling=>E7 (all ret 0); WRONG
variant FAILED (non-vacuous).  Full cbmc-cpp: All tests successful, 96 skipped.

Remaining cluster-B item: cpp11_throw_dtor_unwinding_outer_scope (separate
goto-convert outer-scope-unwinding issue, still KNOWNBUG).

## Cluster B dtor_unwinding_outer_scope — diagnosis (2026-07-13)

N5008 [except.ctor]/1-3, [except.throw]/4: every automatic object whose scope is
exited during unwinding is destroyed before the catching handler runs.  cbmc
misses destructors of objects in scopes exited *between the innermost enclosing
try and the actual catching handler*.

Experiments (g `~G` must run; g++/clang++ both ret 0):
  * V2 throw directly in the SAME try as g  -> SUCCESS (works).
  * V3 throw directly in an INNER try, g in the outer try, inner catches A only,
    B caught by outer -> FAILURE.
  * V1 throw in a callee f(), g in the outer try, no inner try -> FAILURE.
So the trigger is NOT the function boundary; it is that the exception is caught
by a handler that is NOT the innermost enclosing try, so it crosses scope(s)
holding automatic objects.

Mechanism (verified in --show-goto-functions of the original test):
  * goto_convert.cpp convert_expression(throw): unwind_destructor_stack runs
    destructors only up to cpp_try_scope_nodes.back() = the innermost enclosing
    try IN THE THROWING FUNCTION.  Objects below that node (e.g. g, declared in
    the outer try before the inner try) are not unwound at the throw.
  * remove_exceptions_baset::add_exception_dispatch_sequence emits a FLAT
    dispatch: it scans ALL active catch levels (stack_catch) and jumps directly
    to the first matching handler at any level.  For the original test the
    dispatch after `CALL f()` is `IF type==B GOTO <outer B handler>`, which
    jumps straight past `CALL G::~G(g)` (the enclosing-scope cleanup, which on
    the NORMAL path already runs g's dtor and re-dispatches correctly).
The set of destructors to run depends on WHICH handler catches (dynamic): if the
inner handler had matched, g must NOT be destroyed (it outlives the inner
handler); if the outer catches, g MUST be destroyed.  So no static unwind
end_node is correct -- confirmed: unwinding to the outermost try would wrongly
destroy g when the exception is caught by the inner handler.

Correct fix = level-by-level propagation (NOT a small patch):
  the exception, when unmatched by the innermost try, must flow to that try's
  exceptional-exit / enclosing-scope cleanup (running intervening scope
  destructors, which goto_convert already emits and which are construction-state
  correct via the scope tree) and then be re-dispatched at the next enclosing
  level.  Concretely: (1) goto_convert records, per try, an "exceptional exit"
  target = end of the try body (after the try-body remainder, at the enclosing
  cleanup); (2) remove_exceptions restricts each throw/call dispatch to the
  innermost catch level and routes the unmatched case to that exceptional-exit
  target instead of flat-jumping to an outer handler / function end; enclosing
  levels are then handled by the dispatches already emitted at their cleanups
  (and a dispatch must be added at pop_catch for try levels with no intervening
  call).  Subtlety: the unmatched path must SKIP the remaining try-body
  statements while still running the intervening scope destructors, so it must
  target the try's end, not the call's next instruction.

Risk/scope: remove_exceptions_baset is SHARED with Java (jbmc uses it); Java has
no destructors so only C++ needs the intervening cleanup, but the dispatch
change affects both.  jbmc IS built here, so the change can be validated against
BOTH cbmc-cpp and jbmc regression.  Given the size and the subtle
skip-body-but-run-destructors control flow, this warrants a dedicated,
dual-suite-validated change rather than a rushed patch; left as KNOWNBUG.

## Cluster B dtor_unwinding — FIXED level-by-level (2026-07-14, e9df546551 + c4cc61d3a0)

Implemented the level-by-level propagation design:
  * goto_convert_exceptions.cpp convert_try_catch: per-try exceptional-exit
    landing (skip + unwind_destructor_stack(try_entry_node -> enclosing try node
    or 0) + propagate-marker THROW "#exception_propagate"), registered on the
    push-catch as pseudo-entry EXCEPTIONAL_EXIT_TAG ("@exceptional-exit",
    defined in remove_exceptions_base.h).
  * remove_exceptions_base.cpp add_exception_dispatch_sequence: when innermost
    level has the pseudo-entry -> dispatch ONLY that level's handlers (universal
    catch(...) = default target), unmatched -> GOTO exceptional exit.  Chaining
    to enclosing levels is implicit: the propagate marker sits after this try's
    CATCH-pop, so its own dispatch sees the enclosing level as innermost.
    instrument_throw: propagate marker => dispatch + turn_into_skip (in-flight
    state untouched); real throws unchanged.
  * Key correctness pts: no static unwind depth is correct (dtor set depends on
    WHICH handler catches, dynamically); throw-site unwinding still handles
    throw-in-handler (cpp_try_scope_nodes at handler time = enclosing try);
    DEADs come from the base pass's locals insertion at the propagate dispatch.
Verified: outer_scope KNOWNBUG -> CORE; new cpp11_throw_dtor_unwinding_levels
CORE (3-level order innermost-first, no early destruction on inner match,
rethrow unwinds enclosing scope) -- all cross-checked g++ + clang++; WRONG
variant FAILED.  Full cbmc-cpp green (96 skipped).  Java: 54 exception dirs run
before AND after -- identical 11 pre-existing failures (branch baseline), zero
regression from this change.

REMAINING gap (KNOWNBUG cpp11_throw_dtor_unwinding_call_site): the exceptional
edge at a CALL site runs no destructors -- objects constructed between try entry
and a throwing call, and locals of intermediate no-try functions, are never
destroyed.  Fix needs guarded unwind blocks after possibly-throwing calls
(goto_convert emitting placeholder-guarded cleanup that the pass rewires);
separate piece of work.

NOTE: jbmc baseline on this branch has 11 pre-existing failing exception tests
(catch1/test_catch_super, exception-cleanup, exceptions{1,2,4,5,9,22,26,27},
nondet_initialize_exception_handler) -- unrelated to this change, verified by
stash/rebuild/rerun.

## Call-site unwinding — FIXED (2026-07-14, fda2531167 + tests commit)

Implemented guarded call-site unwind cleanups (design (a) from the level-by-level
work):
  * do_function_call (goto_convert_function_call.cpp) calls
    emit_cpp_call_unwind_cleanup (goto_convert_exceptions.cpp): after a
    possibly-throwing call (last instr is a CALL; CPROVER_-prefixed callees and
    unwind-emitted dtor calls excluded) with a REAL pending destructor call
    (DEAD-only scope entries don't count) between current scope and innermost
    try/function base, emit: `IF #cpp_unwind_guard-true GOTO cont; <dtors>;
    PROPAGATE; cont:` and flag the CALL "#cpp_unwind_cleanup_follows".
  * Construction-state window: cpp front-end lowers `T x(args)` as DECL
    (registers dtor) + separate arg-eval + ctor-call statements =>
    pending_construction_start/symbol members exclude the object until its ctor
    call converts (matched via address_of(symbol) first arg) or the decl_block
    ends (trivial/absent ctor).  unwind start-override needs explicit
    save/restore of scope_stack current node (otherwise later registrations
    attach to the walked-down node -- b's dtor vanished in `G a, b;`).
  * "#unwind_path" marking (emit_exceptional_unwind) for ALL exceptional-unwind
    dtor calls (call-site cleanups, try exc-exit landings, throw sites): the
    pass must NOT add in-flight dispatch after them (it hijacked control to the
    handler after the FIRST dtor, skipping the rest -- latent in yesterday's
    landings, masked by 1-object tests).  [except.terminate] justifies no
    dispatch: throwing dtor during unwinding terminates.
  * remove_cpp_exceptions::initialize_globals: pass-created globals are now
    initialized at the FRONT of __CPROVER_initialize (generated pre-pass;
    nondet inflight derailed cpp_dynamic_initialization ctor loops =>
    Constructor9/14, cpp20_compare_header failures -- a LATENT bug exposed
    because cleanups make the pass run on previously exception-free programs).
  * NO mode gate in the cleanup: function symbol mode is 'C' on this branch even
    for C++ functions; the real-dtor-call check confines to C++.
Verified: call_site KNOWNBUG -> CORE; new cpp11_throw_dtor_call_site_order CORE
(ctor-throws exact set + reverse order); g++/clang++ agree on all; WRONG FAILS.
Full cbmc-cpp green (95 skipped).  jbmc exception dirs: identical 11 pre-existing
failures.  Cluster B is now COMPLETE (rethrow + level-by-level + call-site).

## cpp11_unique_ptr_member_enable_if — re-diagnosed (2026-07-14)

The KNOWNBUG has MORPHED: the documented enable_if_t<FALSE> hard error
([temp.inst]/2 concretization of the =delete'd deleter ctor template) is FIXED
by this session's template work.  Remaining failure bisected to a single root:

  std::unique_ptr<C> p;  =>  p.get() != nullptr  (nondet!)

The default ctor is a CONSTRUCTOR TEMPLATE (`template<typename _Del=_Dp,
typename=_DeleterConstraint<_Del>> constexpr unique_ptr() noexcept : _M_t(){}`).
Its specialization symbol is created (symbol table: Type ok, Value EMPTY/nil,
Flags: macro) but the inline body is never instantiated => silent no-op ctor =>
member tuple stays nondet.  Everything downstream (V2-V5: move-assign,
move-ctor, reset, release; delete preconditions "must be dynamic object";
"deallocated object" derefs) follows from nondet initial pointer.  V1 (direct
`unique_ptr<C> p(new C(5))`) WORKS (that ctor gets a body).

Evidence: --show-goto-functions has CALL unique_ptr(this) but NO body for it
(dtor HAS a body); --show-symbol-table shows the ctor symbol with empty Value.
NOTE: no "no body for callee" warning is printed for it (silent!) -- worth
fixing the diagnostics in any case.

Hand-written replications (ctor template w/ default args + SFINAE constraint,
nested DeleterConstraint alias, =delete'd sibling overloads) all WORK.  cvise
attempts (value-bug oracle, g++ compile+link+ASan-run):
  * drifted to a DIFFERENT real bug: a declared-only partial spec with
    kind-mismatched non-type param (`template<long> struct _Tuple_impl<_Idx,_Head>;`
    vs primary `unsigned long`) kills get<0>'s body ("no body for callee",
    silent wrong value).  Kept at /tmp (not committed; secondary lead).
  * with a no-"no body" guard, drifted into a UB artifact (returning address of
    by-value param; clang segfault) => rejected per faithfulness rule.
  * -Werror=return-local-addr doesn't catch that shape (static member fn);
    reduction abandoned -- the real trigger needs the libstdc++ lazy-completion
    path, consistent with cluster A.

Conclusion: cpp11_unique_ptr_member_enable_if is now definitively a cluster-A
instance (deferred member-body instantiation).  Added minimal KNOWNBUG
cpp11_unique_ptr_default_ctor_null (assert default-constructed is null;
g++/clang++ runtime-verified); updated the stale test.desc (old disallowed
pattern kept as regression guard).  The cluster-A fix (source member bodies on
odr-use; nil-body recovery in cpp_instantiate_template.cpp ~3900 currently only
covers out-of-class .tcc definitions, not inline member templates) should flip
BOTH, plus map/tuple.

## cpp11_unique_ptr_default_ctor_null — FIXED (2026-07-14, 7ba91b7d3f + tests)

NOT cluster A after all!  Probe-driven root-cause (temporary env-gated fprintf,
all removed): the ctor-template body WAS instantiated and convert_function ran,
but typecheck_code FAILED inside and the failure was SWALLOWED by the
system-header suppression in cpp_typecheck_function.cpp (catch(int) ->
value.make_nil() -> silent no-op ctor).  Disabling the suppression exposed:
  "found no match for symbol '__uniq_ptr_data'" for the member init `_M_t()` --
candidates lacked a default ctor.  __uniq_ptr_data declares ONLY defaulted move
members + `using __uniq_ptr_impl::__uniq_ptr_impl;`.  Per N5008
[namespace.udecl]/2 (P0136) the using-decl inherits ALL base ctors incl. the
default ctor; [class.inhctor.init]: initialization by an inherited default
ctor == a defaulted default ctor of the derived class.  CBMC's inheriting-ctor
import (cpp_typecheck_compound_type.cpp ~2519) SKIPPED base default ctors while
setting found_ctor=true -> class not default-constructible at all (even the
plain `struct D:B{using B::B;}; D d;` failed!).

Fix: record inherited_default_ctor in the import loop; track
found_own_default_ctor at ctor declarations (zero/all-defaulted params); gate
the implicit-default-ctor synthesis on
  (!found_ctor || (inherited_default_ctor && !found_own_default_ctor)).
Base copy/move ctors stay excluded ([over.match.funcs.general]/9).

Verified: default_ctor_null KNOWNBUG -> CORE; new header-free
cpp11_inheriting_default_ctor CORE (D plain / E move-suppressed / F own-ctor
precedence + parameterized inherit) -- g++/clang++ runtime cross-checked; full
suite green (95 skipped).

REMAINING (separate bugs):
  * cpp11_unique_ptr_member_enable_if still KNOWNBUG: move-ASSIGNMENT of
    unique_ptr still loses the value (operator= has a body now; next layer down,
    possibly release()/reset() through tuple get<0> reference-return).
  * cpp11_inheriting_constructor still KNOWNBUG: PARAMETERIZED inherited ctor
    value semantics (flag/value not set) -- distinct from default-ctor fix.
  * The system-header typecheck failure swallowing (make_nil, no diagnostic)
    masks real bugs -- consider a verbose-mode diagnostic.

## cpp11_unique_ptr_member_enable_if — FIXED end-to-end (2026-07-14)

Continuation of the inheriting-default-ctor fix; three more defaulted-member
gaps found by layer-wise bisection (reset/release worked; move-ctor and
move-assign failed):
  1. default_cpctor base init always sliced source to `const Base&` -> base
     COPY ctor selected for defaulted MOVE ctors ([class.copy.ctor]/15 wants
     xvalue -> move ctor; __uniq_ptr_impl(&&) nulls source).  Fix: Base&& slice
     when is_move.
  2. Base mem-initializer named base by unqualified name -> "symbol '_Head_base'
     does not uniquely resolve" in tuple's EBO hierarchy; swallowed by syshdr
     suppression => _Tuple_impl<0,...> move ctor silently nil ("no body").
     Fix: cast target from resolved b.type() + record #base_type on the
     mem-init (mechanism already used by full_member_initialization).
  3. Defaulted operator= NEVER elaborated (only ctors were) -> empty body,
     nondet return.  Fix: new convert_function block elaborates via
     default_assignop_value with is_move threading; base assignment on the move
     path uses an EXPRESSION assignment (overload-resolves to base operator=,
     running __uniq_ptr_impl::operator=(&&)'s reset+null) -- the frontend
     code_frontend_assignt used by the copy path is a direct subobject copy
     and caused a double delete.
Debug technique: env-gated syshdr-suppression disable + targeted probes (all
removed).  Suite green 94 skipped; member_enable_if + new cpp11_unique_ptr_move
CORE; g++/clang++ runtime cross-checked.

Remaining KNOWNBUGs: cluster A (map/tuple no-body), cpp11_inheriting_constructor
(parameterized inherited ctor values), cpp20_apple_libcxx_basic,
cpp23_expected_basic, cpp11_regex_match, cpp20_iterator_traits_category,
cpp11_throw_dtor_unwinding (none left in cluster B).

## cpp11_inheriting_constructor — FIXED (2026-07-14)

Bisection: plain inherited ctors worked (morning's work); inherited ctor
TEMPLATES failed (V3) -- they are not struct components, so the import loop
never saw them, and cpp_constructor fell back to aggregate init (dropping
args).  Two-part fix:
  1. cpp_typecheck_compound_type.cpp import block: register the base's
     constructor-template TEMPLATE ids (base scope lookup by base_name) in the
     derived class's scope under the derived name -- same mechanism as
     instantiate_template's member-fn-template registration.  Overload
     resolution then instantiates them; the instantiated base ctor initializes
     the base subobject via the `this`-upcast call ([class.inhctor.init]).
  2. cpp_constructor.cpp: `has_inherited_constructor` flag (set at import)
     ORed into the has_user_ctor aggregate-init gate ([dcl.init.aggr]/1 C++17:
     inherited ctors make the class a non-aggregate).
Verified: original KNOWNBUG -> CORE (--cpp20); new header-free
cpp11_inheriting_ctor_template CORE (plain + class-template + own-ctor
precedence), all g++/clang++ runtime cross-checked.  Full suite green, 93
skipped.

Remaining KNOWNBUGs: cluster A (cpp20_map_basic, cpp11_map_insert,
cpp17_tuple_basic), cpp20_apple_libcxx_basic, cpp23_expected_basic,
cpp11_regex_match, cpp20_iterator_traits_category,
cpp11_throw_dtor_unwinding_call_site is CORE now -- checking list: also
cpp11_unique_ptr tests all CORE.

## cpp17_tuple_basic — diagnosis sharpened (2026-07-14), still KNOWNBUG

Fresh reproduction after today's fixes:
  * Direct `std::tuple<int,double,char> t(1,2.0,'a')` PASSES now.
  * make_tuple matrix: ALL arity<=2 PASS (tuple<T1,T2> partial spec);
    ALL arity>=3 FAIL (variadic primary).  No "no body" warning (silent).
  * With syshdr suppression disabled: converting make_tuple's body fails with
    "found no match for symbol '__result_type'" (the return-type typedef
    tuple<__decay_and_strip<_Elements>::__type...>), backtrace shows
    _ImplicitCtor/_ExplicitCtor/_TCC constraint aliases instantiated with
    UNRESOLVED `__decay_t<signed_int>` argument types and
    __enable_if_t<FALSE,bool> => constraints wrongly false, body dropped,
    nondet return.
  * Old (2026-07-13) braced-init call-pack root note is STALE (that bug was
    fixed; the residual is this alias-resolution issue).
  * Hand replications (struct-with-nested-alias-typedef pack expansion;
    member alias templates over constexpr constraint fn; combined) all PASS.
  * cvise x2 (sharper oracle second time: exact swallowed-error signature +
    unresolved-__decay_t marker) both reduced to clang++-rejected artifact
    skeletons => drifted; trigger tied to further real-header detail
    (candidates: the tuple(allocator_arg_t,...) ctor family, the tuple<T1,T2>
    partial spec coexisting with the primary, __is_final/__empty_not_final in
    _Head_base selection, or the sheer alias nesting depth of __decay_t via
    __conditional_t).
Debug hack (CBMC_DBG syshdr-suppression disable) applied temporarily and
REMOVED; tree clean.  This remains the practical route into cluster A: fixing
the arity>=3 alias-pack resolution would flip tuple_basic and likely help
map_basic/map_insert.

## cpp17_tuple_basic — instrumentation session (2026-07-14 evening)

Layered root-cause via probes (ALL removed):
  * FOLD probe (cpp_typecheck_expr constexpr fold): arity 3 folded
    __is_implicitly_constructible<>() (EMPTY args) vs arity 2's full args.
  * AMB probe (template_map.apply cpp_name template-args walker): ident=_Args
    was_pack=1 via matches_empty_pack, with NO _Args in pack_args_map and
    deferred_own_pack_names.count(_Args)=1 -- collapsed against STALE
    same-named zero entries (std::template::NNN::_Args=0 from unrelated
    earlier builds; flat-map V2 violation).
  * FIX (committed 408608ba8d): matches_empty_pack returns false for
    deferred_own_pack_names members ([temp.alias]/2 + [temp.inst]/2).
    Constraints now fold with full args.  For tuple the VERDICT is unchanged
    (empty __and_<> vacuously true) so the test does not flip, but
    argument-dependent constraints would fold wrongly without it.
  * LAYER 2 (remaining, from candidate dump with syshdr suppression disabled):
    `__result_type(...)` ctor resolution: forwarding ctor shows `? &&`
    (its _UElements pack NOT expanded to 3 params) and the const _Elements&...
    ctor shows const STRIPPED (`__decay_t<T> &`).  Both are member ctor
    TEMPLATES of the instance -- their parameter substitution at arity>=3 is
    the next target.  Note template_map.apply's member-walk explicitly skips
    ctors ("have their own empty-pack handling in cpp_instantiate_template")
    -- that ctor-specific path is where the const/expansion loss must be.
  * The stale-pack precondition could not be recreated header-free in
    isolation (needs a same-cascade instantiation history), so no separate
    KNOWNBUG test for layer 1; the tuple KNOWNBUG covers the stack.

## tuple_basic layer 2 — MINIMAL REPRODUCER FOUND (2026-07-14 late)

cpp17_ctor_template_cross_pack_constraint (KNOWNBUG, header-free, 35 lines).
Essential ingredients (each verified by single-dimension toggling):
  1. ctor template of a variadic class template, constrained via SFINAE
     default template arg `enable_if_t<TCs<Es...>::template ok<Us...>(), bool> = true`;
  2. the constexpr callee `ok` is a MEMBER fn template of a SECOND class
     template instantiated over the class pack (free constexpr fn => PASS);
  3. `ok`'s body uses its OWN pack: `sizeof...(Us)` (body using only the
     class pack or a constant => PASS ... note: `return true` also PASSes;
     `sizeof...(Us)==1` REPRODUCES);
  4. construction inside a FUNCTION TEMPLATE's instantiated body
     (direct construction in main => PASS).
NON-essential (all toggled out): fwd/forwarding of args, the typedef R, the
member alias hop (ImplicitCtor), the `bool V` default param, arity >= 2
(arity 1 reproduces!), forwarding-reference vs by-value pack params.
Failure mode: "found no match for symbol 'tup'" during mk's body conversion
=> swallowed => mk bodyless => nondet.  Direct main-scope construction works,
so the defect is in evaluating the cross-template constexpr constraint (with
the callee's own pack) while inside another instantiation's body conversion —
likely the eager constexpr member-fn conversion path in
cpp_instantiate_template.cpp (~4561) or the constexpr-eval in
cpp_typecheck_expr.cpp (~4552), where the enclosing (mk) template_map is
active and the callee's own pack `Us` must be bound from the explicit args.
Flipping this KNOWNBUG should flip cpp17_tuple_basic (and possibly the map
tests).  Suite green, 94 skipped (new KNOWNBUG added).

## cpp17_ctor_template_cross_pack_constraint — FIXED (2026-07-14, 3a941e1d07)

Root: at fn-template SFINAE default-argument evaluation
(guess_function_template_args, non-type-default branch ~7480), the deduced
parameter pack's ELEMENT TYPES were absent from the template map (only its
SIZE was pre-recorded), so an explicit-arg pack expansion in the constraint
(`ok<Us...>()`) collapsed to `ok<>()` -- folded over no args -> ctor rejected
-> "no match" -> swallowed -> caller bodyless (nondet).  [temp.deduct]/5.

ARCHITECTURE LESSON: binding the pack elements UNCONDITIONALLY before the
defaults loop regressed cpp17_tuple_get_two_pack_ctor_3elem (a CORE test whose
two-parallel-pack constraint only resolves against the enclosing map).  Final
fix = try historical order first, RETRY ONCE with the deduced pack bound (in a
cpp_saved_template_mapt frame) on failure.  Both tests pass; suite green (94
skipped).

Side-find (new KNOWNBUG cpp17_fold_comma_single): unary right fold over comma
with a ONE-element pack mis-expands to `true` (multi-element correct).

cpp17_tuple_basic: STILL KNOWNBUG (third layer).  With layers 1-2 fixed, the
real make_tuple still fails "no match for '__result_type'"; probes show all
minimal variants (incl. __valid_args-style member-fn default + alias hop + V,
M9/M10) now PASS, so the residue is yet another real-header detail --
next suspect: the noexcept(__nothrow_constructible<_UElements...>()) specifier
on the forwarding ctor, or the _ImplicitDefaultCtor FALSE fold seen for
tuple<int,int,int> (its __is_implicitly_default_constructible wrongly FALSE).

## cpp17_fold_comma_single — FIXED (2026-07-14 night)

Root: the fn-param-pack expansion in instantiate_template (which also rewrites
fold nodes) is gated `pack_arguments.size() != 1`; for N==1 the fold node
survives into the body and c_typecheck_expr.cpp's residual-fold fallback
(`expr = true_exprt()`, line ~559) degrades it to TRUE.  Fix: N==1 pass
rewriting unary folds to their pattern and binary folds to one op application
([expr.prim.fold]/2).  Covers +, &&, comma, binary; g++/clang++ verified.

Side-find: N==0 (empty pack) instantiation loses the whole BODY ("no body for
callee empty_and<>()") -- pre-existing at HEAD, distinct path (pack-removal).
Filed as cpp17_fold_empty_pack KNOWNBUG ([expr.prim.fold]/3 identities).
Also note: the residual-fold fallback in c_typecheck_expr.cpp remains a
silent-wrong-value trap; consider a warning or hard error there once the
remaining fold paths are fixed.

## cpp17_fold_empty_pack — FIXED (2026-07-14 night)

Root (probe-verified): for N==0 the pack parameter is already REMOVED from the
instantiated declaration, so the body-expansion block (which rewrites fold
nodes) never runs (pack_idx=-1) and residual folds degrade via the
c_typecheck_expr fallback; the body conversion then loses the value (nondet).
Fix: in the pack_sz==0 path, rewrite residual unary folds to their
[expr.prim.fold]/3 identities (&&->true, ||->false, else 0 approximating
void()) and binary folds to their init operand; plus an empty-expanded_names
guard in the general fold expander (OOB indexing hazard).  Safe scoping note:
any fold left in the body at this point folds over THIS function's own empty
pack -- enclosing-class-pack folds were expanded during class instantiation.
Covers &&/||/binary/comma; g++/clang++ verified; suite green 93 skipped.
Fold trilogy complete: N==1 (comma_single), N==0 (empty_pack), N>=2 (already
worked).  The c_typecheck_expr residual-fold fallback (silent `true`) is now
only reachable via genuinely unhandled shapes; still worth a diagnostic.

## cpp11_throw_dtor_unwinding_call_site follow-up — indirect calls FIXED (2026-07-14 night)

The named test was already CORE (fixed this morning).  Boundary probing found
the two residual gaps I predicted in the original design notes: VIRTUAL calls
and FUNCTION-POINTER calls skipped the call-site cleanup.  Root:
remove_function_pointers / remove_virtual_functions rebuild the CALL code for
their dispatch chains, LOSING "#cpp_unwind_cleanup_follows"; the exception
pass then added per-concrete-call dispatch that jumped to the handler before
the cleanup (goto-verified for the fn-pointer case).  Fix: both passes carry
the attribute onto rewritten calls; dispatch-chain branches all jump to
t_final which precedes the cleanup, so one cleanup guards all.  Loop-scoped
objects already worked.  New CORE test cpp11_throw_dtor_indirect_call
(virtual + fn-pointer + loop; g++/clang++ verified).  cbmc-cpp green (93
skipped); jbmc exception+virtual+lambda dirs: identical 11 pre-existing
failures, zero regression.

## Cluster A instrumentation session (2026-07-14 late night)

Fresh reproduction: signature SHARPENED by today's fixes -- operator[] has a
body now; only _M_emplace_hint_unique<...> (member fn template, out-of-line
defined) lacks one.  Probe-driven layer analysis (all probes removed):
  * map case: body PRESENT at instantiation, through typecheck_member_function,
    and at add_method_body queueing (value=code).  TWO add_method_body calls:
    the second dropped by the methods_seen dedupe.  The first entry drains via
    the SECONDARY deferred-fixpoint loop in typecheck_method_bodies (~line
    895+), which lacked the main drain's preprocessing (#fn_template_type map
    restore + #expanded_param_packs expansion) => convert fails ("symbol
    '__args' is unknown", swallowed) => make_nil => "no body".
  * FIX COMMITTED: extracted prepare_deferred_method_body (the ~430-line
    preprocessing block) and called from both drains.  __args error GONE.
  * REMAINING map layers: "void-typed symbol not permitted" during conversion
    (next unpeel target), then whatever follows.
  * Minimal (cpp11_out_of_line_member_template_pack, NEW KNOWNBUG): simpler
    shape fails EARLIER -- body nil already at typecheck_compound_declarator
    ENTRY (never attached).  The forward-decl body recovery (~2583
    same_template_signature parent-scope search) does not find out-of-line
    MEMBER template definitions for this shape; libstdc++'s case works at
    attachment (template_methods carries it) but my minimal's doesn't --
    attachment-path difference worth its own probe next session.
  * Boundary: arity>=2 with pack fails; arity 1 and non-pack OK (the $k
    renaming path).
Suite green 94 skipped.  Next steps: (1) unpeel "void-typed symbol" on map,
(2) fix out-of-line attachment for the minimal, (3) re-run map/tuple.

## cpp11_out_of_line_member_template_pack — FIXED (2026-07-15 early)

Root (probe chain FWD->REG->TM): the out-of-line definition lives ONLY as a
template_methods entry of the enclosing class template (owner
`template.tree<Type0>`, entry base emplace, value present); there is NO scope
TEMPLATE id for it (REG probe: scope_only=0), so neither the instance-scope
forward-decl recovery (~2583; parent-candidates=1 = only itself) nor the
class-instantiation deferred recovery (runs only for deferred_typechecking
entries at class-instantiation time) ever attached it.  The instance's fresh
member-template symbol stayed bodyless.

FIX: in instantiate_template's member-fn-template branch, when the declarator
value is nil, search template_methods across template symbols with the OWNER
matched (class base-name comparison between `<class-instance>::template.<m>`
and the entry's owning `template.<class><params>`); attach the raw body and
adopt the definition's parameter names ([dcl.fct]/3).  First filter attempt
(n_md > n_cls param-count heuristic) was WRONG (the stored template_type holds
only the member's own list) -- TM probe showed the entry rejected; replaced by
the owner match.

Verified: minimal -> CORE; suite green 94 skipped.  Map/tuple still fail on
their NEXT layers ("void-typed symbol not permitted" for map -- unchanged by
this fix since libstdc++'s attachment already worked via a different route).

## Map residual blocker — MINIMAL REPRODUCER (2026-07-15 early)

cpp11_is_swappable_unevaluated (KNOWNBUG).  Chain established via VTS probe +
cvise (22-line skeleton, clang-rejected, hand-rebuilt):
  * "void-typed symbol not permitted" = local `__tmp` of std::swap<void>,
    instantiated COLLATERALLY from the UNEVALUATED probe
    decltype(swap(declval<_Tp&>(), declval<_Tp&>())) in __is_swappable
    ([temp.inst]/5 violation: unevaluated operands need declarations only).
  * Ingredients (verified by construction): the real two-overload __declval
    chain + the variadic enable_if<and_<is_swappable<E>...>> tuple-swap
    overload + an inline friend swap.  Without the variadic overload in the
    set, no reproduction.
  * Observability: a deleted-copy type makes the (wrongly instantiated)
    definition ill-formed and poisons the probe => even is_swappable<int>
    mis-evaluates FALSE.  In the map, the collateral instantiation aborts the
    enclosing member's conversion (the remaining "no body" on
    _M_emplace_hint_unique after the drain-parity + attachment fixes).
  * FIX DIRECTION: the constexpr/SFINAE evaluation paths (cpp_typecheck_expr
    ~4552 eager convert; instantiate_template function branch) must not
    convert/instantiate definitions when the call is inside an unevaluated
    operand (decltype/sizeof/noexcept context tracking), or at minimum the
    default-template-arg SFINAE evaluation must tolerate the collateral
    failure without poisoning the probe result.
Suite green 94 skipped (new KNOWNBUG added).

## is_swappable root cause CORRECTED + FIXED (2026-07-15)

The [temp.inst]/5 unevaluated-operand theory was WRONG.  Bisection of the
KNOWNBUG (b1..b12, c1..c8, d1..d4 in /tmp, reproduced down to 4 lines):

    struct wrap { typedef true_type type;
                  static const bool value = type::value; };  // value nondet!

* The swap<int>/swap<NoCopy> definition conversions observed earlier came
  from the innocent deferred drain, NOT from the probe (CF/FFI probes).
* Real defect: the in-class STATIC MEMBER INITIALIZER reading a class-local
  typedef (qualified or not, decltype or not) was type-checked
  mid-elaboration: the C type-checker can't resolve cpp_names, and the C++
  route ran outside the class scope; the failure was swallowed (sfinae
  guard), leaving sym.value as a raw cpp_name => nondet reads downstream.
  N5008 [basic.scope.class] requires earlier-declared members (typedefs) to
  resolve.  NB: static member initializers are NOT complete-class contexts
  ([class.mem.general]/9 list) -- later-declared siblings stay invisible in
  g++/clang++.
* FIX (b86fecf1b0, cpp_typecheck_compound_type.cpp + cpp_typecheck.h):
  1. route cpp_name-bearing initializers through the C++ type-checker,
     entering the class scope (cpp_save_scopet + id_map go_to);
  2. if still unresolved, queue (member, class) on
     deferred_static_initializers (previously DEAD machinery -- declared,
     drained at typecheck_compound_body end, but never populated!) and
     re-type-check in class scope at end-of-class.
* Collateral: cpp20_apple_libcxx_basic KNOWNBUG -> CORE (real libc++
  <optional>/<string>/<vector> verify in ~16s; traits no longer nondet).
  cpp11_is_swappable_unevaluated -> CORE.  New CORE
  cpp11_static_member_init_class_scope (distilled shapes).
* Map trio STILL KNOWNBUG, new residual: operator[] return-value
  dereference failures (dead object / bounds / invalid address) in
  cpp20_map_basic + cpp11_map_insert; cpp17_tuple_basic fails its layer-3
  make_tuple ctor resolution as before.

Suite green, 92 skipped.  Commits b86fecf1b0 (src), tests commit after.

## cpp11_map_insert FIXED -> CORE (2026-07-15)

Five-layer peel, each layer bisected to a header-free minimal (all now CORE
tests) and fixed per N5008:

1. swap<void> collateral (m4, 78 lines): [temp.deduct.type]/8 -- pack form
   mismatch (P=tuple<_Elements...>& vs A=int*) must FAIL deduction, not
   resurrect the pack as empty.  Fix: tag nil-poisoned pack args
   "#deduction_failed" at the nil->unassigned conversion; the empty-pack
   default-application branch rejects.  Test cpp11_pack_mismatch_not_empty.
2. _Tuple_impl<0,int&&> ctor + _M_head dropped (s9-s12, 6 lines!):
   [expr.ref]/6 -- member access naming a reference member is an LVALUE;
   reference_binding treated implicit derefs of non-symbol rvalue refs as
   xvalues (fix: exempt ID_member).  Plus [over.best.ics.general]/2 -- the
   unguarded typecheck_side_effect_function_call at
   cpp_typecheck_conversions.cpp:~1777 hard-failed a non-viable concrete
   ctor candidate (fix: SFINAE-guard + continue, mirroring site 1871).
   Test cpp11_rvalue_ref_member_lvalue.
3. _M_emplace_hint_unique bodyless (e1/e7, 50 lines): [temp.variadic]/5 --
   the drain's pack expander renamed only the FN param pack (a->a$k) and
   left the TYPE pack whole in `forward<A>(a)...`, so per-element forward
   deduction failed.  Fix: subst_type_pack in prepare_deferred_method_body's
   expand lambda.  Test cpp11_pack_expansion_decl_init.
   Debug chain that found it: gdb catch throw armed via a convert_function
   name-matched global + breakpoint on a noinline marker fn in the catch;
   the escaping throw was resolve() via cpp_constructor/typecheck_decl.
4. pair piecewise ctor unresolvable (q3, ~25 lines): [temp.deduct.type] --
   a full specialization instance records EMPTY (specialization-relative)
   ID_C_template_arguments; deduction read it and bound packs empty.  Fix:
   preserve ID_full_template_args across elaboration (compound_type swap
   save/restore) + prefer it in guess_template_args.
   Test cpp11_pack_deduction_explicit_spec.
5. two-pack swap in instantiation (p1): [temp.param]/14 -- pair's
   piecewise ctor has TWO deducible packs; the flat pseudo-instance arg
   list can't encode the split, and template_mapt::build's single-pack
   arithmetic SWAPPED them.  Fix: record "#deduced_packs" on the
   pseudo-instance in guess_function_template_args, replay before the
   winner's instantiate_template, bypass single-pack arithmetic when
   n_packs>1.  Test cpp11_piecewise_ctor_two_packs.
   PLUS: the provide_stdlib_bodies 'construct' model blanket-assigned
   args[0] into *ptr (piecewise_construct_t into pair -> symex type
   mismatch abort); gated to the exact same-type 3-param case.

Result: cpp11_map_insert VERIFICATION SUCCESSFUL in ~1.4s -> CORE (old
"BMC scaling" note was wrong -- the formula was big because of
mis-instantiated code).  Suite green, 91 skipped.

RESIDUALS (documented, not fixed):
* cpp20_map_basic: --cpp20 with NO unwind bound; full unwinding of
  _Rb_tree loops >10min.  KNOWNBUG note refreshed.
* sizeof...(EMPTY_PACK) inside an arithmetic mem-initializer expression
  mis-evaluates (w4 probe shape: `first(t1.v + int(sizeof...(A2)))` with
  A2 empty read t1.v as 0).  Kept out of the piecewise test.
* Raw OTHER statements (member_initializer / cpp-using) remain in UNCALLED
  emitted functions (e.g. _Rb_tree_const_iterator default ctor never
  converted because never odr-used, body emitted unconverted).  Dead code
  today, but would crash symex if ever reached; consider dropping
  unconverted bodies at clean_up.
* cpp17_tuple_basic unchanged (1 of 7 fails; layer-3 make_tuple ctor
  resolution as before).

Commits: conversions (expr.ref/6 + best.ics), method_bodies (variadic/5),
resolve+compound_type+template_map (3 pack fixes), stdlib construct gate,
map_insert flip, cpp20_map_basic note.

## cpp20_map_basic session (2026-07-15 afternoon): 4 fixes, 2 CORE tests

Diagnosis path: unbounded run loops forever in _Rb_tree_decrement's model
(symex explores nondet-shaped tree).  Bisected `m[1]=42; assert(m[1]==42)`
(mb2): the READ mis-evaluates because the FIRST insert stored a garbage
key (trace: node storage bytes {3,0,...} -- never written).  Chain: the
allocator construct path produced no body for
allocator_traits::construct<pair, piecewise...>.  Four stacked defects,
each bisected to a header-free minimal (a-series in /tmp):

1. PARSER (parse.cpp rAllocateInitializer): the `...` in a
   new-initializer's expression-list was consumed with a literal TODO --
   `::new(p) _Up(forward<_Args>(__args)...)` could never expand.
   [temp.variadic]/5.  (a3 marker: PRE-body ellipsis count 0.)
2. template_mapt::expand_call_argument_packs recursed into NESTED member
   TEMPLATE declarations during class instantiation, consuming their pack
   expansions against the enclosing map ([temp.inst]/2 gate added).
3. Free-fn instantiation body expander (cpp_instantiate_template
   expand_pack) lacked a declarator-init_args branch; recursion corrupted
   `_Up tmp(forward<_Args>(__args)...)` into ONE
   `forward<_Args>(__args$0, __args$1)` (a9).  [temp.variadic]/5.
4. guess_function_template_args' convertibility pre-filter paired the
   implicit OBJECT argument against the first REAL parameter (skipped the
   `this` param but not the object operand) -- member templates like
   `construct(_Up*, pc_t, tuple<int&&>)` rejected as not-convertible
   (a15, 20 lines).  [over.match.funcs]/2.

Tests: cpp11_member_template_object_arg (fix 4 isolated),
cpp11_pack_expansion_new_init (full allocator chain, needs 1+2+4).
Commits: parse.cpp fix, template_map gate, init_args expansion,
object pairing + tests, map_basic note.

Debug techniques that worked: trace-driven (storage bytes {3,0,..} =
never-written malloc garbage); PRE/PREP body dumps at
prepare_deferred_method_body entry/exit to catch marker loss; gdb catch
throw armed via convert_function-name-matched extern "C" global +
noinline marker fn in the catch to bracket the ESCAPING throw among
hundreds of SFINAE throws.

RESIDUAL (cpp20_map_basic stays KNOWNBUG, note refreshed): std::pair's
piecewise ctor is defined out-of-line in <tuple> as a DELEGATING ctor
(`: pair(__first, __second, _Build_index_tuple<...>::__type(), ...)`);
its instance converts to an EMPTY body (delegating mem-initializer of an
out-of-line two-pack member template dropped), so the key is never
stored; the read-back re-inserts and unbounded unwinding diverges.
NEXT: fix the delegating-ctor initializer of out-of-line member-template
ctors ([class.base.init]/6 delegating constructors); then mb2 should
verify and cpp20_map_basic likely flips (re-time it).
KNOWNBUG test filed: cpp11_piecewise_delegating_ctor (105 lines,
header-free, fails-as-expected).  Bisection within the shape: delegation
to a NON-pack target passes (d7); DIRECT call of the four-pack target
passes (d11); delegation to the four-pack target fails with a single
resolve throw in typecheck_member_initializer -- so the gap is the mixed
four-pack (type+non-type index) deduction in the mem-initializer
context, not delegation per se and not the four-pack ctor per se.

## piecewise delegating ctor FIXED -> CORE (2026-07-15 evening)

Six-part fix chain (each bisected header-free; commits in order):

1. #deduced_packs machinery recorded only TYPE pack elements; NON-type
   index-pack VALUES (pack_expr_map) added to annotate+replay
   ([temp.variadic]/8).  Minimal: e3/e7 (mixed type+non-type pack target
   called from any instantiated body).
2. Out-of-line definition adoption (3 sites: typecheck_class_template_member
   merges x2 at ~675/~1045, instantiate attach x2 at ~4300/~4560) copied the
   BODY but not the MEM-INITIALIZER-LIST -- [class.base.init]/1 says the
   ctor-initializer is part of the definition.  Minimal: f1 (out-of-line
   delegating, literal index_tuple args).  KEY probe insight: the value was
   attached by the THIRD site (search which one fires!).
3. Same-named overloaded member-template definitions (pair's TWO piecewise
   ctors) confused by base-name-only matching in the attach blocks; added
   param-count discrimination ([over.load], [dcl.fct]/3).  Minimal: z2
   (BOTH ctors out-of-line).
4. Empty-pack mem-init argument removal dropped `sizeof...(EMPTY)` mentions
   (breaking `_Build_index_tuple<sizeof...(_Args2)>::__type()`, shifting
   the delegation args); refined to drop only refs OUTSIDE #sizeof_pack
   ([temp.variadic]/4 vs /8).  Minimal: d10 (build_index<sizeof...> args).
5. Drain-side: #fn_template_packs persisted on the method symbol +
   replayed in prepare_deferred_method_body (flat #fn_template_args can't
   encode multi-pack splits); plus the same sizeof...-aware empty-pack
   arg removal on member_initializer statements in the prepared body
   (`second(forward<_Args2>(get<_Indexes2>(t2))...)` with empty packs ->
   `second()`).
6. [expr.static.cast]/3: static_cast<Base&&>(derived_lvalue) -- the
   std::_Tuple_impl MOVE ctor shape `: _Base(static_cast<_Base&&>(__in))`
   -- was rejected (exact-type-only rref branch in static_typecast).
   This was EXPOSED as a cpp11_map_insert REGRESSION mid-session (the
   newly-converting piecewise chain finally CALLED tuple's move ctor,
   which was bodyless; moved-to tuple's reference member NULL).  Minimal:
   m2 (25 lines) -> CORE test cpp11_static_cast_base_rref.
   NOTE argument-order trap: subtype_typecast(from, to) checks `to` is a
   BASE of `from` -- the lvalue-ref branch's call is a DOWNCAST check.

Wins verified: cpp11_piecewise_delegating_ctor -> CORE;
`m[1]=42; assert(m[1]==42)` verifies ~1.6s (--cpp11 --unwind 5);
cpp20_map_basic's PROGRAM verifies UNBOUNDED under --cpp11 (0 of 1427).
Suite green, 91 skipped.

RESIDUAL: cpp20_map_basic under --cpp20 still KNOWNBUG -- the C++20
header path constructs the node via std::construct_at/_S_construct
(constexpr allocator_traits chain); key byte again malloc garbage
(storage[0]=64), unbounded decrement walk diverges.  NEXT SESSION: find
which body in the construct_at chain fails/is modeled away under
--cpp20 (same CVF/armed-gdb recipe; check also the `construct` stdlib
model gate for the C++20 shapes).

Debug recipes that worked again: armed extern "C" global + noinline
marker fn breakpoints bracketing the ESCAPING throw among hundreds;
PSM/pack-map dumps at deduction vs build; PRE/PREP body dumps; the
uncaught_exceptions RAII dump for cast failures.

## cpp20 construct_at blocker MINIMAL REPRODUCER (2026-07-15 late)

cpp11_construct_at_pack_args (KNOWNBUG, fails-as-expected, 82 lines,
header-free).  Bisection path from the real map (--cpp20):
* allocator_traits::construct under --cpp20 is constexpr -> is_macro,
  value NIL, its CALL absent from _M_construct_node's goto body;
  std::construct_at absent from the symbol table entirely.
* Distillation: constexpr is NOT required (h-series: the constexpr
  member-template h1/h4/h5 all pass); the decltype-SFINAE return and
  noexcept(placement-new+declval) are NOT required (k8); const members
  not required (j5 vs j6); the trigger is a FREE function template
  whose new-initializer expands a pack of >= TWO arguments constructing
  a CLASS-TEMPLATE instance (j7: wrap<int> + wrap(T,T), 20 lines).
  One argument passes (j1/j6/j8).  Failure mode: "no body for callee
  construct_at" -- the instantiated body's conversion fails.
* Likely locus: the FREE-fn-template body expander's cpp_new-initializer
  handling for multi-element packs (the member-template flavour was
  fixed via the parser ellipsis + [temp.inst]/2 gate + init_args branch;
  a4 from that session was never re-run and is this same gap).
* SEPARATE bug found during bisection, not filed yet: a member template
  of a class template with a FOLD over its pack ('*p = (args + ...)')
  drops the call entirely (h3/h6) -- non-constexpr too.  Worth its own
  minimal/KNOWNBUG next session.

Suite green, 92 skipped (new KNOWNBUG added).  cpp20_map_basic desc
links to the minimal.

## construct_at pack-args FIXED -> CORE (2026-07-15 night)

Two fixes (commit: instantiate_template + 2 tests):
1. [temp.variadic]/5 + [expr.new]: free-fn-template body pack-expander
   (cpp_instantiate_template.cpp ~6280) had no cpp_new-initializer branch.
   Added one mirroring the function-call/init_args branches:
   `::new(p) T(forward<Args>(args)...)` now replicates per element.
   cpp11_construct_at_pack_args -> CORE.
2. [temp.inst]/5: void-returning constexpr member fn templates (the C++20
   allocator_traits::construct wrapper) were eagerly converted before the
   deferred body-pack expander ran, resolving the still-packed
   construct_at call and dropping the body.  Root-caused via n8 vs n8b
   (constexpr vs not, identical body/map/annotations -- the ONLY diff was
   the eager attempt).  Gate: defer void-returning constexpr members
   (return_type == ID_empty).  Also confined the eager attempt to an
   inner cpp_saved_template_mapt scope so its forced-empty pack bindings
   don't leak into the add_method_body requeue snapshot.
   New CORE cpp11_void_constexpr_wrapper_defer.

Bisection ladder (all /tmp): h3/h6 (fold-in-member-template drop, still
unfiled bug), k1/k2 (construct_at chain), j1..j8 (arity: >= 2 pack args +
class-template target triggers), n1..n8 (constexpr wrapper isolation),
p1/p2 (decltype-return vs plain-return).

RESIDUAL (narrowed, KNOWNBUG cpp11_construct_at_decltype_return): the
trailing-return `decltype(::new((void*)0) _Tp(declval<_Args>()...))` on
std::construct_at ITSELF fails argument deduction with >= 2 args
constructing a class-template instance ("found no match").  Plain-return
same body works (p2).  This is the sole remaining --cpp20 map blocker.
NEXT: the trailing-return decltype over a pack-expanded new-expression is
evaluated during [temp.deduct.call] deduction; find why the pack-expanded
`_Tp(declval<_Args>()...)` in the return decltype doesn't deduce (likely
the return-type decltype is type-checked before/without the deduced
_Args pack, or the new-expression in a decltype isn't handled by the
deduction-time substitution).  cpp11_map_insert still CORE (no
regression); suite green 92 skipped.

## construct_at decltype-return FIXED -> CORE (2026-07-15 late night)

The residual C++20 std::construct_at blocker: its trailing return type
`decltype(::new((void*)0) _Tp(declval<_Args>()...))` failed argument
deduction with >= 2 args ("found no match").  Bisection (r1..r7):
* r2 plain `_Tp*` return: PASS; r7 non-pack fixed 2-arg decltype-new:
  PASS -> the pack expansion INSIDE the decltype-new is the trigger.
* apply(decltype) calls expand_call_argument_packs, which only handled a
  function_call's ID_arguments; a cpp_new's ID_initializer expression-list
  was never treated as a pack-expansion context, so `declval<_Args>()...`
  kept its `...` and deduction failed.
FIX (template_map.cpp): generalise expand_call_argument_packs to also
expand a cpp_new initializer's expression-list (gate on cpp_new; select
the ID_initializer named-sub as the arg list), mirroring the sibling
body-expander cpp_new branch in cpp_instantiate_template.
cpp11_construct_at_decltype_return -> CORE.

Result: --cpp20 now instantiates construct_at (5 symbols), runs the pair
piecewise ctor, stores the key.  cpp20_map_basic's FRONT END is fully
correct; its remaining non-termination is a pure BMC solver-scaling wall
(at --unwind 5: ~6.5min to build the equation, solver then OOMs), NOT a
conformance bug -- the same program verifies unbounded under --cpp11.
map note reclassified accordingly (stays KNOWNBUG as a performance item).
Suite green, 91 skipped.

Three CORE tests now cover the full C++20 construct_at chain:
cpp11_construct_at_pack_args, cpp11_void_constexpr_wrapper_defer,
cpp11_construct_at_decltype_return.  Still-unfiled lead:
fold-over-member-template-pack drops calls (h3/h6 from the prior session).

## fold-over-member-template-pack MINIMAL REPRODUCER (2026-07-15 late)

The unfiled lead is now filed: cpp17_member_template_fold (KNOWNBUG).
Bisection (g1..g6): free fn + fold PASS (g1/g6); class member + NO fold
PASS (g3); MEMBER fn template + fold REPRODUCES (g2/g4/g5), enclosing
class need NOT be a template.  Minimal g4:
  struct S { template<typename... A> static int sum(A... a)
             { return (a + ...); } };
Root cause: free function templates run instantiate_template's expand_pack
(which has cpp_left_fold/cpp_right_fold/cpp_binary_fold branches -- from
the fold trilogy work); MEMBER function templates run
prepare_deferred_method_body's arg-list/base$k expander, which has NO
fold handling.  So the member body's fold is left unexpanded, the bare
pack name fails to resolve (gdb: resolve throw in typecheck_return of
sum), and the body is dropped.  NEXT: add fold-expression expansion to
prepare_deferred_method_body's expand lambda (or share the
instantiate_template fold logic).  g++/clang++ runtime-verified.

## fold-over-member-template-pack FIXED -> CORE (2026-07-15)

cpp17_member_template_fold flipped KNOWNBUG -> CORE.  Root cause confirmed:
free function template bodies are expanded by cpp_instantiate_template
(which reduces cpp_left_fold/cpp_right_fold/cpp_binary_fold), but MEMBER
function template bodies are prepared by prepare_deferred_method_body
(cpp_typecheck_method_bodies.cpp), which had NO fold handling -- so the
fold's bare pack reference (`a` in `(a + ...)`) was left unexpanded,
failed to resolve, and the whole body was dropped ("no body for callee").

Fix: added a fold-reduction pass to prepare_deferred_method_body, per
N5008 [expr.prim.fold]:
 - unary right fold -> right-associated tree e0 op (e1 op (... op eN-1))  (/1)
 - unary left  fold -> left-associated  tree ((e0 op e1) op ...) op eN-1 (/1)
 - binary fold left-associated, seeded by init                           (/2)
 - empty pack -> operator identity (&& true, || false, comma void()/0)   (/3)
Element source: for N>=2 the replicated params base$0..base$N-1 (count from
#expanded_param_packs or the names); for 0/1 no such params exist (0: no
param; 1: the sole element keeps the plain name `base`), so the count is
taken from template_map.pack_size_map (unambiguous when the member has a
single pack -- gated on pack_size_map.size()==1).  Pitfall hit & fixed:
merging eprec AND the base$k scan double-counted (a=4 for a 2-element
pack); use eprec-or-scan, not both.  Verified arities 0/1/N, right/left/
binary, class-template member, and a WRONG-value negative (must FAIL,
non-vacuous); g++ AND clang++ runtime-verified.  Two commits (src, test);
full suite green (91 skipped, was 92).  Added <util/arith_tools.h> +
<util/c_types.h> includes for from_integer/signed_int_type.

## make_tuple arity>=3 FIXED -> CORE (2026-07-15 late)

cpp17_tuple_basic flipped to CORE.  Two root causes, both fixed:
1. [temp.variadic]/8 CONST DROP: in-class pack replication
   (cpp_typecheck_compound_type.cpp) replaced the whole pattern
   `merged_type[const, cpp_name(_Elements)]` of `const _Elements&...` with
   the raw pack element -> replicated params lost const -> couldn't bind
   rvalues ([dcl.init.ref]/5) -> tuple's converting ctor removed ->
   "found no match for symbol '__result_type'" swallowed as system-header
   leniency -> nondet make_tuple.  Fix: carry pattern const/volatile onto
   the substituted element.  Minimal header-free CORE test:
   cpp11_const_pack_pattern_param (pre-fix: hard CONVERSION ERROR).
2. [basic.scope.temp] NIL-PLACEHOLDER PREFERENCE: lookup_by_suffix
   (template_map.cpp) scored a sibling partial spec's nil `_Tp`
   placeholder above the live binding (scope-path length); nil entries now
   skipped in both type_map and expr_map loops.
Arity boundary explanation: tuple<_T1,_T2> partial spec (arity<=2) takes a
different path.  Debug journey pitfalls: (a) show-symbol-table renders a
typedef'd int as its typedef NAME (looks self-referential but isn't);
(b) symbol_tablet::move inserts a nil-typed dummy first (probe noise);
(c) cvise twice over-reduced to different-defect variants (uninit read;
degraded __valid_args) -- anchor oracles on the precise probe signature
AND verbatim source lines.  LATENT (unfixed, masked): __valid_args
explicit-arg member-overload selection fails in the make_tuple context ->
forwarding ctors dropped (RESOLVE-FAIL-T __valid_args); const& ctor now
matches so end-to-end works.  Worth a follow-up KNOWNBUG if it resurfaces.

## cpp20_iterator_traits_category NONDETERMINISM DIAGNOSED (2026-07-15 late)

The flakiness (1-in-5 FAILED) is ADDRESS-ORDER dependence: with ASLR
disabled (`setarch $(uname -m) -R cbmc ...`) the failure is DETERMINISTIC
(6/6 FAILED) -- use this for all debugging.  Failure mode: the selected
`iterator_traits<vector<int>::iterator>::iterator_category` is
bidirectional_iterator_tag instead of random_access_iterator_tag (probed
via is_same asserts /tmp/it.cpp shape).

Root cause located (not yet fixed): in cpp_instantiate_template.cpp's
partial-specialization search (~line 1830-1925), when several partial
specializations share the same argument pattern and differ only by
requires-clauses -- libstdc++'s __iterator_traits member alias `__cat`
has three such specs (#req___cpp17_input_iterator /
__cpp17_fwd_iterator / __cpp17_randacc_iterator chains) -- the
"more specialized" tie-break is a CRUDE COUNT heuristic
(count_constrained, then arg-list size, then a numeric requires-clause
count via stoi + #C_concept_constraint counting).  When those counts TIE,
the winner is whichever candidate is seen first in
`cpp_scopet::id_sett = std::set<cpp_idt *>` -- POINTER-ordered, hence
ASLR-dependent.  N5008 [temp.class.spec.match]/2 + [temp.constr.order]
require selecting the most-constrained SATISFIED spec via constraint
SUBSUMPTION -- and the proper machinery already exists:
constraint_subsumes / constraint_strictly_subsumes in
cpp_typecheck_resolve.cpp (~line 129-305, used by overload resolution).

FIX PLAN (next turn): in the best_match tie-break, when argument
patterns are equal, evaluate ALL satisfied candidates' requires-clauses
and pick the one whose associated constraint strictly subsumes the
others' ([temp.constr.order]/1); fall back to a DETERMINISTIC order
(e.g. symbol-name comparison) only when subsumption is incomparable
(ambiguity).  Also audit: iterating `id_sett` (std::set<cpp_idt*>)
anywhere selection-relevant is a latent nondeterminism source; consider
name-keyed ordering.  Probes used (all reverted): SPEC-REQ/SPEC-FIRST/
SPEC-BEST in the search loop.

## iterator_traits nondeterminism FIXED -> CORE (2026-07-15 late)

cpp20_iterator_traits_category flipped to CORE.  Fix as planned:
de-anonymized template_constraint_strictly_subsumes (declared in
cpp_typecheck_resolve.h) and used it in instantiate_template's
partial-spec search equal-pattern tie-break, replacing the stoi/count
heuristic; incomparable constraints now tie-break by SYMBOL NAME
(deterministic), never by pointer order.  Verification: 6/6 normal +
3/3 setarch -R runs pass (was 6/6 FAIL under -R); full suite green BOTH
ways (ran suite once normally and once wrapped in a setarch -R shim
script -- useful trick: test.pl -c /tmp/cbmc-noaslr.sh).  89 skipped
(was 90).  Technique note: ASLR-dependent front-end flakiness ->
setarch -R makes it deterministic; grep for std::set<cpp_idt*>
iteration when selection-relevant.

## cpp23_expected_basic FIXED -> CORE (2026-07-15 late)

"conversion from 'void' to 'signed int'" on *e: the VOID partial spec
`expected<_Tp,_Er> requires is_void_v<_Tp>` was selected for _Tp=int.
Probe (REQ-EVAL in instantiate_template's requires eval) showed the
substituted clause simplified to result-id=constant val=0 -- a NUMERIC
c-bool 0, which `is_false()` does not recognize, so satisfied stayed
true.  Fix: `req_copy.is_false() || req_copy.is_zero()`.  NOTE: three
header-free mimics of the is_void_v chain (bool variable template;
is_same_v-based; exact integral_constant/false_type/inline-constexpr
chain h3) all produce a proper `false` and pass PRE-fix -- only the full
libstdc++ chain yields the numeric zero, so cpp23_expected_basic itself
(with headers) is the regression test.  Suite green, 88 skipped (was
89).  ALL THREE queued KNOWNBUGs of this session now CORE:
cpp17_tuple_basic, cpp20_iterator_traits_category, cpp23_expected_basic.

## locale model + defect-hunt + dog-fooding round (2026-07-16)

1. LOCALE ([locale.general]/8 + C99 7.4): modelled the classic ctype<char>
   facet (provide_classic_ctype_char_model in cpp_typecheck_stdlib.cpp);
   __try_use_facet<ctype<char>> override must live in the HAS-BODY section
   (header-inline body) and match base_name by PREFIX (template suffix is
   appended).  CORE test cpp11_locale_ctype_facet.  regex residual = BMC
   scaling only.
2. KNOWNBUG cpp17_default_targ_overload_select: explicit-template-arg call
   to an OVERLOADED member fn template inside a DEFAULT TEMPLATE ARGUMENT
   finds no viable overload (libstdc++ tuple __valid_args shape).
3. FIXED (cpp_instantiate_template.cpp): class-body fold expander (a) broke
   qualified pack patterns `Ts::v` (wholesale type replacement; now
   substitutes only the leading name component with the struct-tag id) and
   (b) had NO cpp_binary_fold branch (parser: sub[0]=left of `op ...`,
   sub[1]=right; pack side determines association).  Both crashed symex
   via static inline member inits.  CORE test cpp17_static_member_fold_init.
4. KNOWNBUG cpp11_chrono_mixed_duration_add: mixed-period operator+ body
   conversion fails (RESOLVE-FAIL `duration`/`__cd`), swallowed -> nondet.
5. FIXED (cpp_instantiate_template.cpp): pack expander created EMPTY
   ID_init_args on every declarator via irept::add-creates-on-absence ->
   typecheck_decl invariant crash on `S x = value;` in variadic template
   bodies.  Found by DOG-FOODING cbmc's own util/symbol_table.cpp +
   simplify_expr_int.cpp (via util/invariant.h backtrace decl).  Reduction
   pitfall: the crash needs cbmc's own preprocessor WITH #line markers
   (system-header leniency is location-dependent); g++-preprocessed or
   marker-stripped sources diverge to CONVERSION ERROR.  CORE test
   cpp11_decl_value_in_pack_body.
6. KNOWNBUG cpp17_optional_string (front-end CRASH):
   optional<std::string> trips make_ptr_typecast precondition (unrelated
   structs) in typecheck_member_initializer of _Optional_payload.  Also
   the root of dog-food failures in simplify_expr.cpp / cmdline.cpp.
   NEXT-fix candidate.

Dog-food set (all OK unless noted): string_utils, parse_options, tempdir,
unicode, version, irep, expr, type, json_parser, std_expr, cpp_parser,
arith_tools, std_types, langapi/language, xml_parser; symbol_table +
simplify_expr_int fixed by (5); simplify_expr + cmdline blocked by (6).
Suite green, 91 skipped.  shared_ptr: BMC scaling only (no front-end
defect; not filed).

## ROADMAP NOTE (user, 2026-07-16): "unit proofs" for CBMC's own code base

Once the current KNOWNBUG backlog is cleared, start constructing UNIT
PROOFS: proof harnesses that accompany selected unit tests (unit/ tree,
Catch2), but -- unlike unit tests, which fully fix all inputs -- take
NONDETERMINISTIC inputs where appropriate and run through CBMC itself.
This applies the usual CBMC-on-C methodology to C++ and, crucially,
dog-food style: within and applied to CBMC's own code base.

Prerequisites / notes from the dog-fooding rounds so far:
- The C++ front end can already parse+convert a good slice of src/util
  (irep.cpp, expr.cpp, std_expr.cpp, type.cpp, cpp_parser.cpp, ...).
- Known blockers to clear first: cpp17_optional_string
  (make_ptr_typecast crash -- blocks any code using
  optional<std::string>, e.g. cmdline.cpp/simplify_expr.cpp);
  cpp11_chrono_mixed_duration_add; cpp17_default_targ_overload_select;
  shared_ptr BMC scaling (affects any harness touching shared_ptr).
- Candidate first harnesses (small, self-contained, value-oriented):
  * util/string_utils (split/strip/escape round-trips with nondet chars)
  * util/arith_tools (from_integer/numeric_cast round-trips over nondet
    integers of bounded width)
  * util/irep (share/detach invariants: set/get round-trip, comparison
    reflexivity/symmetry over small nondet tree shapes)
  * big-int (arithmetic identities over bounded nondet operands)
- Harness shape: a main() that builds bounded-nondet inputs
  (__CPROVER_assume to constrain), calls the unit under proof, asserts
  the property the unit test spot-checks -- yielding a proof over ALL
  inputs in the bounded domain rather than fixed samples.
- Infrastructure idea: a regression/unit-proofs/ suite mirroring unit/
  paths, driven by test.pl with per-harness --unwind bounds; tag slow
  ones thorough.

## chrono + default_targ CORE; optional_string crash fixed (2026-07-16)

1. cpp11_chrono_mixed_duration_add -> CORE.  THREE stacked fixes:
   (a) [temp.deduct]/5+[basic.scope.temp]/2 deduction restricted to the
   deduced template's own parameters (current_deduction_parameters +
   template_map.deduction_parameters + V1 short-name-loop guard) and
   exception-safe cpp_name swap-restore in typecheck_type ([temp.deduct]/8
   no-lasting-effect); (b) [temp.inst]/5 convert_deferred_method_now:
   on-demand conversion of deferred constexpr members needed by constant
   evaluation in default template args (chrono _S_gcd in __divide);
   (c) constexpr evaluator gaps: do-while ([stmt.dowhile] body-first),
   decl initializers ([dcl.init]), expression-statement assigns.  New
   header-free CORE test cpp11_fn_template_param_shadow.
   DEBUG-JOURNEY note: 'same call works in main, fails in fn-template
   body' = deferred-drain ordering/state; census of enable_if<0,...>
   instantiations via a typecheck_template_args result probe pinpointed
   the false conjunct (integral_constant<bool,0> from __is_harmonic).
2. cpp17_default_targ_overload_select -> CORE.  (a) [temp.arg.explicit]/3:
   too-many-explicit-args is now a silent candidate-removal
   (template_arg_kind_mismatch_exceptiont) during overload matching;
   (b) [temp.variadic]/5: member-body fold reducer recognises a
   single-element pack by the method's own (un-replicated) parameter
   name, independent of how many packs are in the map.
3. cpp17_optional_string: CRASH FIXED (still KNOWNBUG for values):
   per-base recovery in typecheck_compound_bases ([class.derived]/2 --
   one failing base no longer drops siblings) + make_ptr_typecast
   degrades to plain typecast on unrelated structs.  Dog-fooding of
   cmdline.cpp/simplify_expr.cpp UNBLOCKED (0 errors).  REMAINING ROOT:
   __is_destructible_impl<basic_string>::type (decltype __test SFINAE)
   fails only inside optional's nested instantiation (fine at user
   level) -> is_trivially_destructible degrades -> _Optional_base bool
   args mismatch.  NEXT session: chase the nested-context decltype
   overload resolution.
Suite green 89 skipped both runs; probes swept; 8 commits this session.

## optional_string residual REDUCED: base NSDMI drop (2026-07-16)

New KNOWNBUG cpp11_base_nsdmi_implicit_ctor (5 essential lines,
header-free): `struct B { bool e = false; }; struct D : B {}; D d;`
leaves d.e NONDET -- the implicitly defined default constructor of a
DERIVED class does not apply the base's default member initializers
([class.base.init]/9.1).  Boundaries: direct base object OK; explicit
`B() = default;` OK; one derivation level suffices.  This is the actual
root of cpp17_optional_string's nondet has_value()
(_Optional_payload_base::_M_engaged = false dropped).  LESSON: the
earlier nested-context trait-SFINAE hypothesis was a red herring for the
VALUE failure -- it only explained the (now-fixed) crash path; cvise on
the cbmc-preprocessed default-construction case isolated the true
observable defect in one round.  Reduction chain: optional<string>
default-ctor (with-headers, 27k lines preprocessed) -> cvise 16 lines ->
hand-bisect 5 lines.  FIX SITE hint: implicit/synthesised default ctor
generation for classes with bases (cpp_typecheck_compound_type ctor
synthesis) vs the working direct-object path; the explicit `= default`
path evidently routes through the working code.

## base-NSDMI drop FIXED -> CORE (2026-07-16)

cpp11_base_nsdmi_implicit_ctor flipped to CORE.  Root cause exactly as
reduced: full_member_initialization's base loop skipped cpp_is_pod bases
entirely, and cpp_is_pod does not model NSDMIs, so a POD-classified base
with a default member initializer got NO initialization in the
synthesized derived ctor ([class.base.init]/9.1 + [class.default.ctor]/3
violated).  Fix (cpp_typecheck_constructor.cpp): for a non-virtual POD
base with has_default_member_initializer, emit member-initializers via
the flattened from_base components (own #default_value -> initialize
from it; type-with-transitive-NSDMIs -> default-construct through
cpp_constructor's recursive NSDMI path).  [dcl.init]/8 subtlety probed
and handled: an explicit EMPTY base initializer (`: B()`) still applies
NSDMIs (value-init); only an initializer WITH arguments supersedes.
Edge cases verified: two POD bases; mixed base+own NSDMIs.
cpp17_optional_string still KNOWNBUG: its optional<string> instance has
ZERO members (`o={ }` in trace) -- the dropped-base-specifier resolution
failure remains the last blocker there.  Commit-hygiene note: an
--amend after a follow-up `git add` landed on the WRONG commit (the
test commit); fixed with `git reset --soft HEAD~2` + separate
re-commits.  Suite green 89 skipped.

## dtor-SFINAE base-specifier blocker: minimal reproducer FILED (2026-07-16)

cpp17_dtor_sfinae_base_spec (KNOWNBUG, header-free, ~40 essential lines):
the decltype-SFINAE destructibility probe as a base specifier
(`struct safe : impl<T>::type` with `typedef decltype(test<T>(0)) type`)
fails to resolve ONLY when elaborated inside a nested
default-template-argument context (payload's `bool = trait_v<T>` inside
base_<T> inside opt<T>); per-base recovery cascades: safe<S> loses its
base -> and_<safe<S>,...> (conditional base needs B1::value) loses its
base -> opt<S> loses base_ -> nondet members.  Works at user level.
Reduction notes: (a) first cvise run with only the has_value anchor
drifted to an EAGER-INSTANTIATION variant (kept at /tmp lost; shape: a
template-id ARGUMENT `__and_<__is_destructible_safe<int>>` eagerly
elaborated though never required to be complete per [temp.inst]/1 --
possibly a second latent defect worth revisiting); (b) precise oracle =
temporary BASE-DROP fprintf probe in the per-base recovery catch +
require BASE-DROP of BOTH the trait class and _Optional_base + FAILURE +
g++/clang accept + runtime OK.  (c) the mimic must stay WELL-FORMED:
using an undefined impl<T::type> made g++ reject once and_ required
B1::value.  Probe reverted before commit.  Suite green 90 skipped.

## dtor-SFINAE base spec + optional<string> FIXED -> CORE (2026-07-16)

Both flipped to CORE.  THREE stacked destructor-resolution fixes
(cpp_typecheck_expr.cpp, cpp_typecheck_resolve.cpp):
1. [expr.prim.id.dtor]+[class.dtor]/1,6: `x.~X()` on a class with only an
   implicit TRIVIAL dtor (no synthesized symbol, POD gate) now uses the
   scalar pseudo-destructor no-op dummy instead of failing resolution.
2. [expr.prim.id.dtor]/2: ~_Tp substitution preferred an arbitrary
   same-short-name flat-map binding (allocator's _Tp!); now prefers the
   binding designating the CURRENT class scope.
3. Angle-unaware rfind("::") in the dtor-name extraction landed inside
   template ARGUMENTS (`~allocator` spelled for basic_string) -- fixed
   angle-aware at both substitution sites; SAME bug pattern also fixed
   in the base-NSDMI member-prefix computation (template-instance bases
   like tag-base_<tag-S> mismatched every component).
LESSON (recurring pattern #3 now seen 3x): any rfind("::")/rfind("tag-")
over template-instance tag names MUST be angle-bracket-aware; grep for
remaining instances would be a worthwhile sweep.
Diagnostics: BASE-DROP probe + blanket T0 tags + DTORSUB probe; all
reverted.  Suite green 88 skipped (was 90).  Remaining KNOWNBUGs are the
two scaling-bound ones only (regex_match, map_basic) -- the KNOWNBUG
backlog of front-end defects is CLEAR, unit-proof work is unblocked.

## dog-food round + FIRST UNIT PROOFS (2026-07-16)

Dog-food: all previously-blocked files now clean; NEW fix: [stmt.label]/1
function-scoped labels (cpp convert_function never reset
labels_defined/labels_used; bigint.cc unblocked); CORE test
cpp98_function_scoped_labels.  OPEN: goto_program.cpp CONVERSION ERROR
(codet default-construction no-match) -- next dog-food target.

UNIT PROOFS landed (regression/unit-proofs, registered in CMake):
- threeval GREEN: 9 Kleene-logic laws over ALL value pairs, 7s.  The
  proof-of-concept for the roadmap: unit-test contract -> bounded-domain
  proof via nondet inputs + __CPROVER_assume.
- strip_string KNOWNBUG: blocked by NEW front-end defect found while
  building it -- cpp11_self_pointer_move_return: move ctor branching on
  the source's self-pointer (SSO shape) + return-by-value -> destination
  clobbered by bitwise copy, pointer targets the dead return temporary.
  This breaks std::string BY VALUE across the board (t.front() after
  `t = make()` reads a dead object) -- HIGH-VALUE fix target.
- bigint_arith KNOWNBUG: solver OOM at 16GiB (digit-vector heap model);
  try SMT backend / field slicing later.
Suite green 89 skipped; ctest unit-proofs 4/4.
LESSON: the unit-proof mission statement held on the very first harness:
building strip_string's proof immediately flushed out a fundamental
front-end defect (SSO move-return) that ordinary feature tests missed.

## minimal reproducers round (2026-07-16)

goto_program.cpp dog-food failure ISOLATED ->
cpp11_delegating_ctor_decl_order (KNOWNBUG): [class.base.init]/6
delegation recognition is DECLARATION-ORDER dependent.  The detector in
full_member_initialization (cpp_typecheck_constructor.cpp ~894) scans
struct components for a constructor whose base_name matches the
mem-initializer; when the delegating ctor is declared BEFORE its
target, no ctor component exists yet -> delegation missed -> members
default-initialized (hard 'found no match' when a member lacks a
default ctor; silent wrong values otherwise).  Reordering (delegator
AFTER target) works today -- the o1/o2 probes prove pure order
dependence.  Real-world shape: goto_programt::instructiont() delegating
to instructiont(goto_program_instruction_typet), _code has no default
ctor.  FIX IDEA: recognize delegation syntactically (initializer names
the class itself) instead of scanning components, or run the check
after all ctor components are added.

cpp11_self_pointer_move_return SHRUNK 25 -> 14 lines: no copy ctor, no
payload, assert directly t.p == t.buf.  Minimality probes: empty branch
body PASSES, unconditional rebase PASSES, `S t = S();` PASSES -- the
defect needs (a) return-by-value through a function AND (b) a
CONDITIONAL overwrite of the pointer member in the move ctor.  The
'bitwise copy clobber' happens only when the move ctor body contains
the conditional assignment -- pointer analysis of WHERE the clobber
comes from (tmp_obj -> t copy) is the next fix step.
Suite green, 90 skipped.

## delegation-order fix + return-by-value elision (2026-07-16)

BOTH targeted defects FIXED, tests CORE, suite green (89 skipped),
strip_string unit proof VERIFIES.

1. cpp11_delegating_ctor_decl_order: detector now compares the
mem-initializer name against the class's injected-class-name
([class.base.init]/2+/6, [class.pre]) instead of scanning ctor
components.  Nested-class tags are qualified (outer::inner) and
template tags carry args -- angle-aware final-component scan (4th
instance of that pattern!).  goto_program.cpp dog-foods clean.

2. cpp11_self_pointer_move_return: THE BIG ONE.  Root cause: SET RETURN
VALUE + return-value passing relocate returned objects BITWISE (3 hops)
and dtor the temporary after copying out.  Fix = new goto pass
elide_cpp_returned_temporaries ([stmt.return]/2, [class.copy.elis]):
hidden result-pointer param (Itanium sret), returned front-end
temporary ($tmp::tmp_obj, instance-range-scoped -- identifiers are
REUSED across unrelated temporaries, whole-body substitution corrupts
them!) substituted by *#result; DECL/DEAD/dead_object/post-return dtor
dropped (caller owns + destroys); call sites pass &lhs (ignored-result:
fresh slot + dtor call).  Non-temporary returns: move ctor iff
implicitly movable ([class.copy.elis]/3 -- REFERENCE-param returns must
COPY; m1 mimic move-only, mv3 ident(const&) both green), else copy,
else assign.  Gate: symbol-table scan for ctor/dtor symbols by this-
param (goto-level struct components have NO method components!).

Chained front-end defects unearthed (each needed for strings by value):
- typecheck_return: wrap the operand BEFORE base implicit_typecast
  ([conv.lval] strips lvalue -> MOVE ctor mis-selected for lvalues);
  implicit move only for id-expression naming non-static local;
  removed the std:: skip (old dtor-chain crash workaround, obsolete).
- reference_binding: lvalue->T&& temp-copy workaround block now rejects
  GENUINE lvalues by form ([basic.lval]: symbol/deref/member/index;
  [dcl.init.ref]/5.4) but still materializes stale-flag prvalues
  (cpp11_restrict_reference's R{5} needs that; flag-only fix broke m1
  via synthesized memberwise copy, form-only-reject broke R{5} -- BOTH
  needed).
- __builtin_memcmp modelled in ansi-c library (char_traits::compare
  stub returned NONDET -> every std::string == failed).  NOTE: library
  functions REQUIRE a matching regression/cbmc-library/<name>/ test or
  the BUILD fails (library-check.stamp) -- symptom: stale binary,
  'no body for callee'.

Debug lesson: trace `t.p=tmp_obj!...` pointers name the DEAD SOURCE
object; --show-goto-functions on make() exposed the ASSIGN hops
immediately.  Value-category bugs manifest as WRONG CTOR SELECTION.

## stage profiling of the scaling-bound tests (2026-07-17)

Method: timestamped phase lines (awk) + 2s RSS sampler; 16GiB cap.

1. bigint_arith (unit proof): front end+goto 1s, symex 1s (9635 SSA
steps, 1787 VCCs) -> **propositional reduction OOM** (14GiB @ ~86s).
--refine and --property single-assertion do NOT help (base constraint
encoding blows, not the property set).  Culprit: 17955 byte_extracts
over HEAP DIGIT ARRAYS (BigInt::digit_add/digit_sub/adjust_size SSA
dominate the equation); dynamic objects with symbolic size flatten
catastrophically.  UNBLOCK IDEAS: fixed-capacity BigInt model for
harnesses, or constrain allocation sizes concretely in the harness
(force adjust_size to a constant), or SMT array theory backend.

2. cpp20_map_basic: front end 5s (16k goto instructions, ~400 fns).
Unbounded: symex runs >15min (2.2GiB, time-bound).  --unwind 6: symex
OOM 16GiB @ ~460s.  --unwind 5 (minimum sound for the R-B tree loops;
unwind<=4 gives spurious FAILURE): symex 33s -> **propositional
reduction >15min no verdict** (~8GiB, stable).  So: symex-heavy AND
encoding/solver-bound at the sound unwind.  Twin bottleneck.

3. cpp11_regex_match: **program-size-driven**: 358k goto instructions,
4233 functions (<regex> fully instantiated).  Front end 28s,
function-pointer removal 76s, then symex grinds >18min @ 5.5GiB without
reaching the solver.  Symex-bound via sheer program size; needs a
lighter regex/locale model or aggressive slicing before symex
(--drop-unused-functions? reachability slice) to have any chance.

Summary: three DIFFERENT dominating stages -- encoding (bigint),
symex+encoding (map), symex/program-size (regex).  None is a front-end
defect; all are verification-performance items.

## widened dog-fooding + unit proofs round 2 (2026-07-17)

Dog-food batches 1-5 (mp_arith, source_location, message, format_type,
byte_operators, pointer_offset_size, goto_program, goto_function,
remove_returns, json_parser, cmdline, options, expr_util, rename,
replace_expr, replace_symbol, prefix_filter, piped_process, lispexpr,
lispirep, string2int, string_container, show_goto_functions, json, xml,
format_number_range): ALL CLEAN except:
- find_symbols.cpp -> cpp17_hash_node_vector_alloc KNOWNBUG (hash-node
  allocator rebind poisons later vector<K> instantiation, order-dep;
  minimized) + cpp11_unordered_set_insert KNOWNBUG (_Insert CRTP mixin
  member body never instantiated -- 'no body', count wrong; minimized
  to unordered_set<int> --cpp11).  Fix leads: deferred-method-body
  instantiation for mixin bases (same family as
  convert_deferred_method_now), template-map contamination.
- goto_trace.cpp + initialize_goto_model.cpp: 'missing type in template
  argument' at optional:754 (converting-ctor _Requires SFINAE with
  defaulted _Up=_Tp) -- NOT yet minimized (simple optional<string>
  probes pass); also graph.h output_dot_generic no-match.  OPEN leads.

Unit proofs: capitalize CORE GREEN (34s; size/first-char/tail/
idempotence over printable len<=3).  escape KNOWNBUG: solver OOM 16GiB
-- `result += c` = data-dependent heap reallocation = the symbolic-size
dynamic-object bit-blasting blow-up (bigint class).  LESSON: harness
tractability heuristic -- single-allocation transforms (capitalize,
strip_string via substr) verify; incremental-append transforms (escape,
BigInt digits) hit the encoder wall.  Suite green 90 skipped;
unit-proofs 3 CORE green + 2 KNOWNBUG.

## solver follow-ups + optional-SFINAE isolation (2026-07-17)

1. bigint_arith SMT: --z3 >30min, --cvc5 >20min, both no verdict
(encoding cheap, SOLVING diverges).  cvc5 first failed on a CBMC SMT2
bug: datatype selector names with "::" unquoted -> Parse Error.  FIXED
(smt2: quote datatype selector names via convert_identifier; new
helper datatype_selector_name, 5 emission sites).  cvc5 1.2.1 installed
per CI (wget release zip -> /usr/local/bin).
2. cpp20_map_basic REFRAMED by --paths lifo: verdict in ~1min (vs >15
min one-shot no-verdict) -- and the counterexample exposes the REAL
blocker: _Rb_tree_insert_and_rebalance is in libstdc++'s COMPILED
tree.cc -> havoc'd -> tree linkage nondet -> can NEVER verify.  Needs a
model of tree.cc entry points (BST-link without rebalancing).  desc
updated.
3. cpp11_regex_match desc: full stage profile + unblock candidates
captured.
4. optional:754 SFINAE lead ISOLATED (source-level function bisection
beat cvise: 90s/test x 87k lines was hopeless; killed it).  Trigger:
`return {};` in ANY function returning optional<T> (even optional<int>)
-- MY pre-base return wrap (yesterday) fed the empty braced-init-list
to converting-ctor deduction; _Requires SFINAE default arg then hit
"missing type in template argument" + wrong emptiness semantics.
FIXED per [stmt.return]/2 + [dcl.init.list]/3.5: value-initialize the
returned temporary.  CORE test cpp17_optional_return_empty_brace.
LESSON: a fix that reroutes expressions through new_temporary must
handle ALL braced-init shapes ({} = value-init, {args} = list-init).
5. goto_trace.cpp residual isolated header-free ->
cpp98_static_member_private_ctor KNOWNBUG ([class.access.general]/7:
out-of-class static member definition has MEMBER access; front end
judges from namespace scope).  12 lines.
Suite green 91 skipped; smt2_solver suite green (bit-to-fp1 'failure'
was a stale binary).

## tree.cc models + real map blocker (2026-07-17 afternoon)

The four tree.cc models ALREADY EXIST (cpp_typecheck_stdlib.cpp,
earlier session) and FIRE -- yesterday's "havoc'd insert_and_rebalance"
was a misread of the model's own parameter ASSUMEs.  Real blocker
isolated from the lifo counterexample: cpp20_pair_converting_ctor
KNOWNBUG -- C++20 pair's requires+explicit(bool) converting ctor
pair(U1&&,U2&&) instantiates WITHOUT a body (macro-flagged constexpr
symbol, nil value, never deferred-queued; probe: nil=1 deferred=0
macro=1); symex havocs it.  _M_get_insert_unique_pos's _Res(__y, 0)
(literal 0 -> rref_signed_int) selects it.  cpp17 pair (enable_if)
fine.  FIX LEAD: instantiation path for requires-constrained +
explicit(bool) members must queue the deferred body (family:
convert_deferred_method_now / _Insert mixin defect).  6-line repro:
pair<nodet*,nodet*> b(y, 0) under --cpp20.

## four-KNOWNBUG session (2026-07-17 afternoon)

1. cpp11_unordered_set_insert: THREE front-end defects fixed on its
chain (all committed): (a) instantiate_template deferred-drain tag-strip
unbounded rfind("::") -- 5th instance of the angle-aware-scan pattern!
(b) [class.access.base]/4-5 friendship for derived-to-PRIVATE-base
conversion; new plumbing cpp_typecheckt::access_judgment_scope (RAII in
cpp_constructor around its class-scope switch) since candidate matching
runs with current scope = candidate's class; CORE test
cpp98_friend_private_base_conversion.  (c) [stmt.pre]/6 if/while
condition-declaration name leaked into enclosing block; CORE test
cpp98_condition_decl_scope.  Insert path now converts FULLY; residual =
bucket-chain walk divergence (unwinding assertion in
_M_find_before_node at --unwind 30, garbage node pointers) -- STILL
KNOWNBUG, needs isolation of the insert-side linking.
2. cpp98_static_member_private_ctor FIXED -> CORE:
[class.access.general]/7, out-of-class static member initializer now
typechecked with the member's class scope re-entered
(cpp_declarator_converter::handle_initializer wrap).  goto_trace.cpp
dog-foods CLEAN now.
3. cpp17_hash_node_vector_alloc: two sound lookup improvements (tag-
aware scope-of-T filter; elaborate-and-retry) but root cause remains:
a COMPLETED template instance's scope lacks member templates that were
not used during its own instantiation ('rebind' registered only for
instances whose rebind was used then).  REAL FIX: [temp.names]/3
primary-template-scope fallback with instance template map.  KNOWNBUG,
full diagnosis in desc.
4. cpp20_pair_converting_ctor: requires-clause CALL atoms
(_S_constructible<...>()) now constant-folded in candidate filtering
([temp.constr.atomic]) -- unviable candidates no longer win.  RESIDUAL:
the RIGHT ctor's body still silently fails conversion (nil symbol,
syshdr leniency) -- pair members nondet.  KNOWNBUG, next step in desc.

LESSON: fixing a "no body" symptom often unlocks a CHAIN of further
defects (unordered_set: 3 fixed + 1 residual); commit each layer
separately and keep the KNOWNBUG with an updated diagnosis until the
test genuinely verifies.  Suite green 91 skipped throughout.

## residual reproducers round (2026-07-17 evening)

All three residuals now have minimal reproducers:
1. cpp20_requires_class_param_atom (header-free, first-try mimic!):
requires atom referencing ENCLOSING CLASS template param unevaluable;
the s3-vs-s4 bisect proved it: non-template class folds fine, class
template param does not.  FIX: extend the requires evaluator's
name_to_type with the class instance's
ID_C_template/ID_C_template_arguments.
2. cpp17_member_template_completed_instance: cvise triumphed where
hand mimics failed 3x -- 26k preprocessed lines -> 39 header-free lines
in ~15 min (the 90s baseline fear was wrong: reduced cases fail fast,
so cvise accelerates as it shrinks).  Every piece of the alias chain
(__uset_hashtable shape, hash<vector> partial-spec DECLARATION) is
needed for the instantiation order.  Recovery keeps VERIFICATION
SUCCESSFUL, so the KNOWNBUG fails via a FORBIDDEN-pattern line --
useful test.desc technique for diagnostic-only defects.
3. unordered_set residual is NOT front-end: _M_need_rehash/_M_next_bkt
live in compiled hashtable_c++0x.cc, havoc'd (61 no-body hits) ->
garbage bucket count -> divergent bucket walks.  Fix = model both in
cpp_typecheck_stdlib.cpp (like tree.cc): _M_next_bkt >= max(n,13) +
_M_next_resize bookkeeping; _M_need_rehash compares against
_M_next_resize.  Functional semantics don't depend on the exact count.
Suite green 93 skipped.

## rehash models + requires fix (2026-07-17 late)

1. cpp11_unordered_set_insert FIXED -> CORE (insert/dup/count/erase
verify UNBOUNDED in ~1.5s!).  Three more layers: (a) models for
compiled-library _Prime_rehash_policy::_M_next_bkt (max(n,13), mutable
_M_next_resize) + _M_need_rehash (load-factor-1 doubling) --
[unord.req] bucket count is performance-only; (b) deferred_typechecking
erase on SUCCESSFUL body conversion (out-of-line members re-enter the
set at declarator conversion; clean_up nil'd CONVERTED bodies --
_M_deallocate_node_ptr); (c) [expr.prim.id.dtor]/1 +
[basic.lookup.qual]/6 dtor-via-TYPEDEF-name (`__n->~__node_type()`):
sub-resolver in object's class scope then postfix-expression context
(access_judgment_scope, set by typecheck_expr_member).  DEBUG WIN: the
blanket line-tagged throw-0 probe found the silent failure in minutes.
2. cpp20_requires_class_param_atom FIXED -> CORE:
[temp.constr.decl]/3 -- map the enclosing class instance's
ID_C_template/ID_C_template_arguments into the satisfaction check's
name substitution (member params shadow, [temp.local]).  libstdc++
pair still KNOWNBUG: atoms are consteval static member CALLS -- fold
returns unknown (next lead: instantiate _S_constructible with class+
member args).
3. cpp17_member_template_completed_instance NOT fixed; diagnosis
sharpened: the primary's class-BODY scope doesn't exist either (BFS
proved it); member class templates get scope entries only when USED
during an instance's own instantiation.  REAL FIX: register member
class-template declarations at instance-body conversion (mirror the
template_methods walk's registration of member FUNCTION templates).
Suite green 91 skipped.

## residual reproducers round 2 (2026-07-17 night)

1. cpp20_requires_static_call_atom KNOWNBUG filed (header-free, ~30
lines, first-try repro): requires(ok<U2>()) calling a constexpr static
member template whose body uses the CLASS parameter -- the call-atom
fold returns unknown.  Pins the exact remaining pair/map mechanism;
inline-atom variant already CORE.  FIX: fold must type-check the callee
with class+member template maps.
2. Member-template registration: 4th hand-mimic (competitor + alias
chain + value-dependent default arg + dependent-scope consumer) still
PASSES -- 39-line cvise reduction confirmed minimal; the incomplete
struct K + hash<vector> partial-spec declaration + allocator_traits::
value_type member interlock is irreducible by hand.  Registration fix
(instance-body conversion) remains the identified repair.
3. unordered_set: NO residual (fully CORE since the rehash models).
Suite green 92 skipped.

## consteval atoms + per-member recovery (2026-07-17 night 2)

1. cpp20_requires_static_call_atom + cpp20_pair_converting_ctor FIXED
-> CORE.  Four-part fix in the satisfaction check's call-atom fold:
manifestly-constant-evaluated context ([temp.constr.atomic]/1 --
constexpr evaluator only folds under constant_expression_context);
prepare_deferred_method_body for the eagerly-converted callee
([temp.inst]/1 member map on top of class map); c_bool constant
recognition (bool spelled c_bool -- is_true/is_false miss it!);
foldable forms extended to ==/!= atoms BUT results only TRUSTED when
type-check emitted no recovered diagnostics (unrestricted
generalization broke std::span -- concept-id atoms error-recover into
bogus constants; [temp.constr.atomic]/3 keeps unknown safe).
2. cpp17_member_template_completed_instance FIXED -> CORE by
PER-MEMBER ERROR RECOVERY in typecheck_compound_body during implicit
instantiation ([temp.inst]/11 tolerance; user code stays strict).  The
REAL root cause wasn't registration at all: a mid-body throw (silent
qualified-lookup SFINAE) dropped every FOLLOWING member of the
instance, incl. member class templates.  STEP-probe technique (per-item
index + uncaught_exceptions watcher) found it in minutes.
find_symbols.cpp dog-foods CLEAN.
3. cpp20_map_basic next frontier: pair value lost in the sret handoff
through _M_get_insert_hint_unique_pos's tail call (__pair_base
"ignoring typecast" suspect).  cpp17_hash_node_vector_alloc residual:
push_back dropped via silent enable_if<0,void> SFINAE
(_S_use_relocate constexpr use in return type not covered by the
stdlib model override).
DEBUG HAZARD LOGGED: an auto-inserted braceless-if probe before
`it.get_writeable_symbol().value.make_nil()` made the nil
UNCONDITIONAL -- always brace-wrap injected probes (the misleading-
indentation -Werror caught it; earlier T0 inserter's paren-heuristic
also produced one stray-brace repair).
Suite green 89 skipped.

## residual reproducers round (2026-07-18)

1. **alignas layout defect FOUND (major)**: CBMC ignores alignas (and
_Alignas, __attribute__((aligned))) in struct layout -- sizeof
`{alignas(int) char}` = 1, g++ says 4.  This is __aligned_membuf =
the value storage of EVERY _Rb_tree_node and _Hash_node.  It, not the
"pair sret handoff", is cpp20_map_basic's primary poison (old desc
theory retracted).  Fix lead: struct layout code in ansi-c (affects C
too) -- honour ID_alignment padding for members.
2. Secondary map defect: synthesized copy assignment of an
empty-base-only class emits struct-to-base typecast; prop encoder's
`ignoring()` drops the whole constraint ("warning: ignoring
typecast").  Only reproduces combined with a punned deref shape --
kept combined in cpp11_map_value_loss_reduced.
3. push_back drop sharpened: bare `unordered_set<K>*` DECL (no
object/insert) kills vector<K>::push_back (enable_if<0,void> on
_S_use_relocate; stdlib override covers bodies, not constexpr uses in
return types).
4. qualified-typedef member drop reduced to ~50 header-free lines
(needs the __uset_hashtable alias chain; 15-line version passes).
TECHNIQUE: cvise interestingness for false positives MUST gate on
valgrind + UBSan-clean runtime, or it reduces to UB programs that
"fail" legitimately (two wasted rounds).  cbmc --preprocess (not g++
-E) for faithful preprocessed input; add extern __CPROVER_assert decl
for the g++ leg; -std=gnu++20 for the Q-literal branches.
test.pl -K semantics: KNOWNBUG descs encode the DESIRED behavior;
under -K "successful" means the test currently FAILS (correct).
Suite green 93 skipped.

## four-fix round (2026-07-18 evening)

1. **alignas layout FIXED** (3 independent losses): parser.y's
`_Alignas(type)` action set ID_type_arg on the DISCARDED $3 (fix: build
the C11 6.7.5 _Alignof equivalence into ID_size on $$); cpp
rIntegralDeclaration swapped away the alignas merged into
declaration.type() by rDeclaration (fix: merge pre-collected
specifiers, skipping the empty-id merge_types seed -- merge_types with
a default-constructed typet creates merged_type{x, ""}!); cpp never
folded ID_C_alignment to a constant (fix in typecheck_type, mirroring
c_typecheck_type, error-count-restoring for dependent contexts) and
never ran add_padding for explicitly-aligned structs (gate extended
from bit-field-only).  cpp11_alignas_member_layout +
cpp11_map_value_loss_reduced CORE; the encoder "ignoring typecast"
disappeared too (constants fold with correct layout).
2. **[temp.deduct]/2 clean-slate FIXED** -- the big one:
convert_template_parameter's lookup_by_suffix fallback captured an
ENCLOSING instantiation's same-short-name parameter for an explicitly
UNASSIGNED deduction variable.  unordered_set<K>'s _Alloc=allocator<K>
leaked into stl_bvector.h's hash<vector<bool,_Alloc>> pattern during
hash disambiguation -> hybrid vector<bool,allocator<K>> -> truncated
cached __alloc_traits -> vector<K>::push_back dropped + value_type
unknown.  Fix: fallback only when the exact id is WHOLLY UNKNOWN to
the map (present-but-unassigned = active deduction context).  THREE
tests flipped: push_back_after_unordered_set_decl,
qualified_typedef_member_drop, hash_node_vector_alloc (fully green).
TECHNIQUE: backtrace(3) + dladdr fbase-relative offsets + addr2line
resolved a 40-frame template-machinery recursion in minutes; the
instantiation-stack probe at class_template_symbol showed the hybrid's
creation directly.
Remaining map_basic failure at unwind 6: _Rb_tree_insert_and_rebalance
__p->_M_left derefs (next frontier; NOT the alignas/pair layers).
Suite green 89 skipped (4 flips this round).

## map rebalance round (2026-07-19)

Rebalance derefs were NOT a rebalance bug: three front-end defects
upstream, all fixed (suite green 88 skipped):
1. GNU `__alignof__(expr)` in C++ parsed the operand as a TYPE-ID only
-> object names failed resolution -> silently alignment 1 in
`alignas(__alignof__(_M_t))` = __aligned_membuf!  Fix: cpp
typecheck_expr_alignof override mirroring the sizeof disambiguation
(wantt::BOTH).  cpp11_alignof_expr_member CORE.
2. requires-satisfaction evaluator blind to c_bool constants (again!
same class as the call-atom round) -> FALSE clauses "unknown" -> the
unsatisfiable candidate KEPT and it WON overload resolution.
Recognize integral constants at eval entry -- but ONLY for
candidates without concept-ids in their constraints (concept
error-recovery fabricates zero constants; gate via "#concept_" in the
mangled name; ungated version broke span AGAIN).
cpp20_requires_trait_value_atom CORE.
3. throwing whole-clause typecheck kept the candidate ([temp.constr.
atomic]/3 says unsatisfied) -- pair(node, 0) selected the CONVERTING
ctor whose _S_constructible atom threw pre-body-preparation; literal
0 forwarded into a pointer member = the map __res garbage.  Fix:
post-throw RETRY of the tri-state eval on the substituted clause
(call atoms only).  Wholesale reject-on-throw broke 9 concepts tests;
the retry compromise keeps all green.
cpp20_requires_static_call_retry CORE.
Remaining map layer: PIECEWISE pair construction chain loses the
value (key reads 0, operator[] ref lands at offset 12 not 4; ALL
pointer checks green).  Reduced to cpp20_map_piecewise_value_loss
(171 header-free lines).  Small hand mimics of delegation+pack-init
PASS -- needs the full tuple machinery; next round starts there.
TECHNIQUE: cvise gates need "no CBMC deref FAILUREs" (excludes
UB-shaped reductions) + self-contained runtime via cxa stubs
(bodyless libstdc++ externs like _Rb_tree_insert_and_rebalance let
reductions exploit CBMC's silent havoc of undefined functions --
gate rejected those once bodies were appended).  Also: watch for
`cp x backup` AFTER x was already clobbered (lost the first 124-line
reduction; conversation log had it).
SIDE GAP noted: aggregate init `itert{&x}` rejected ("found no match
for symbol") when the struct has a user-declared dtor -- untracked.

## residual capture sweep (2026-07-19 evening)

1. NEW KNOWNBUG cpp11_aggregate_temporary_with_dtor: `itert{&g}`
(braced functional cast, [expr.type.conv]/2 -> aggregate init per
[dcl.init.aggr]/1) fails "found no match for symbol" as soon as ANY
dtor is declared (user or =default) -- the front end routes braced
temporaries of dtor-bearing classes to ctor overload resolution.
Matrix: decl-form `itert it{&g}` WORKS; no-dtor temporary WORKS; ALL
standards affected.  Fix lead: the temporary-object construction path
must fall back to aggregate init when the class is an aggregate
(check where cpp_constructor/typecheck_expr_function_call handles
braced init of class prvalues).
2. Bodyless-function havoc: NO diagnostics gap -- `no-body` FAILURE
properties fire for plain, std::-namespaced, and reference-taking
bodyless functions in cpp mode.  The map-round degenerate reduction
passed my cvise gate because the gate greped only for
assertion/dereference failures -- LESSON: interestingness gates
should reject on ANY non-target FAILURE property (add `grep -qE
"no-body.*FAILURE" && exit 1`).
3. Sweep: piecewise value loss already captured
(cpp20_map_piecewise_value_loss); _Rb_tree_node_base sizeof-28 is the
documented no-ABI-padding modeling choice (self-consistent); NN_ tag
prefixes are cpp_type2name display artifacts.

## aggregate + piecewise round (2026-07-19 late)

1. cpp11_aggregate_temporary_with_dtor FIXED -> CORE: #is_implicit_ctor
marker (rides on decl.type() in default_ctor; copy/move inherit) +
braced-temporary aggregate gate skips implicit ctors
([dcl.init.aggr]/1).
2. cpp20_map_piecewise_value_loss FIXED -> CORE (the 171-line
reduction): root cause was NOT the pack-expansion mem-init at all --
forward_as_tuple's body `tuple<_Elements...>(__args...)` is C++20
P0960 PARENthesized aggregate init (tuple has no matching ctor!);
unsupported -> body silently dropped -> key havocked.  THREE parts:
paren-aggregate fallback (ctor-first per [dcl.init.general]/16.6.2.2)
in explicit_constructor_call + retry-reroute in typecheck_side_effect_
function_call (catch around typecheck_function_expr; recursion guard
paren_aggregate_in_progress; error-count snapshots BEFORE the try —
capturing after the emission left phantom CONVERSION ERRORs twice);
deleted-implicit-DEFAULT-ctor semantics ([class.default.ctor]/2:
conversion failure of an implicit this-only ctor = ID_noaccess
deletion, NOT an error — implicit copy/move excluded, deleting those
changed overload selection and broke Constructor13); cpp_constructor
user-ctor scan now marker-based instead of SHAPE-based (this-only
skip also skipped USER default ctors — combined with my single-operand
extension that aggregate-initialized Constructor13's `base_type(10)`).
3. cpp20_map_basic next layer: second lookup's equivalent-keys path
derives the returned reference from __pos._M_node == NULL (iterator
equality/decrement).  Fresh frontier, desc updated.
LESSON: for multi-edit rounds run the FULL suite before flipping —
the Constructor13 breakage was 2 edits deep in interaction; bisecting
by reverting one file at a time with the saved copies was fast.

## capture sweep 2 (2026-07-19 night)

1. Probed adjacent gaps to the P0960 round: deleted implicit COPY ctor
(private base copy) -- WORKS (no capture needed); P0960 ARRAY form
`int a[3](1,2,3)` -- WORKS; paren-aggregate with FEWER args than
members -- FAILED ([dcl.init.aggr]/5 trailing value-init) and FIXED in
both cpp_constructor lowering paths (zero_initializer for missing
elements; @most_derived true).  New CORE test
cpp20_paren_aggregate_trailing_init.
2. The map null-hint layer RESISTS sanitizer-gated cvise: reductions
keep converging to guard-eliminated intra-object UB (writing through
the header base object downcast to node -- ASan is blind to overlay
within one global) and textual anchors (`grep "== end()"`,
`key_comp`) get satisfied vacuously (kept as discarded expression /
variable name).  The layer stays covered by cpp20_map_basic
(KNOWNBUG, desc has the diagnosis: second lookup's equivalent-keys
path derives the returned reference from __pos._M_node == NULL).
Next attack should be direct trace analysis of the real map, not
reduction.
Suite green 88 skipped.

## map final layer (2026-07-20) -- cpp20_map_basic IS CORE

The 8th and final layer: std::pair's piecewise delegation target
`first(forward<_Args1>(get<_Indexes1>(__tuple1))...)` never converted.
TWO defects:
1. [temp.variadic]/5: mem-init pack expansion only rewrote one-element
struct_tag TYPE packs by name; mixed reference-type + NON-TYPE index
packs kept raw names + ellipsis.  New
expand_member_initializer_packs_in_body (both whole-initializer and
per-ARGUMENT ellipsis; type+expr packs in lockstep) wired into
prepare_deferred_method_body (after its #fn_template_packs replay) AND
the eager constexpr-member conversion path.  NOT at instantiation time
(packs not yet bound there; eager expansion broke fwdref ctors).
2. [temp.deduct]/8: template-arg typecheck failures while
candidate-matching now convert to template_arg_kind_mismatch_
exceptiont (type/ambiguous/non-type branches) -- get<0> vs by-type
get<T> overload aborted resolution before.
DIAGNOSIS PATH: trace showed pair ctor entered but wrote nothing ->
goto dump: delegated-to ctor bodyless -> 12-line header repro
(pw.cpp) -> gdb catch-throw backtraces (fatal = last before FNFAIL
marker) -> NOMATCH probe named the unresolved '_Indexes1' -> body
dump showed surviving ellipsis.  Header-free bisect: by-type overload
NECESSARY (gt4 fail vs gt5 pass).
HAZARDS HIT: (a) probe-strip DELETED an adjacent real fix (labels
function-scope block sat between probe and try) -- diff EVERY stripped
file against HEAD before rebuilding; (b) cpp11_recursive_forwarding_
tuple_ctor fails STANDALONE but passes under test.pl (pre-existing
flakiness, confirmed at HEAD) -- always confirm regressions at HEAD
before hunting; (c) instantiation-time expansion sites looked right
but broke fwdref packs -- prepare/eager are the correct points.
Suite green 88 skipped.  Map history complete: 8 layers, each CORE.

## Dog-food widening + unit proofs round (2026-07-20)

Sweep: src/util 117/117 convert (after fixes), big-int/langapi/json/
xmllang/assembler 14/14, goto-programs 67/69.  Four fixes:
1. [class.copy.assign]/12 bases-by-TYPE in copy_parent + POD cpctor
   branch (union path needs union_tag_typet -- struct_tag broke
   cpp11_union_constructor).  _Hashtable_ebo_helper double-base shape.
2. [namespace.unnamed]/1: anon branch RETURNED before converting body
   items (everything in `namespace {}` dropped).  Fixed per-scope name
   #anon_ns through the regular machinery + using-directive.
3. [over.match.oper]/3 member-strip mis-fired on EXPLICIT
   `operator==(o)` calls; gated on operator_expr_lookup_depth RAII in
   operator_is_overloaded.  Only strip in operator-expression lookup.
4. extern template basic_string<char>: .tcc members were NONDET stubs.
   THREE cooperating gaps: swap-completion not recorded in
   instantiated_with (replay skipped the instance); member_exprt
   callees never pulled deferred_method_bodies (only symbol callees);
   instantiate_matching_member_body matched bodies across ALL
   templates by base name (string_view's rfind attached to
   basic_string's).  Owner filter = template id after "template." up
   to '<' vs class base name.
DIAGNOSIS: unit proof over get_base_name caught rfind returning
nondet -- proofs ARE the dog-food test.  Probe ladder: symbol table
value -> replay convert -> declconv final_id (retry has $constthis) ->
handle_initializer sym_val -> drain convert "OK" but val nil'd by
syshdr sfinae guard -> env-gated guard skip exposed the real error
("string_view.tcc:101 ... __n unknown").
NEW SOLVER-GATE LESSON: `warning: ignoring typecast` after
"converting SSA" = boolbvt::conversion_failed havocs a value; the
unit-proofs forbidden pattern catches it.  trim_from_last_delimiter
KNOWNBUG documents the derived-to-base struct VALUE cast gap
(_Alloc_hider EBO); fix would lower to base-component extraction.
Proof-harness rules: NO std::string::find(char) in SPEC code (memchr
model loses provenance); use plain loops.  edit_distance KNOWNBUG:
nfa set/vector symex scaling.
Suites: cbmc-cpp green 87 skipped; unit-proofs green 4 skipped.

## KNOWNBUG capture round (2026-07-20 afternoon)

All four uncaptured findings now have minimal tests; one became a FIX:
1. memchr had NO MODEL (either spelling) -- root of the "string::find
   provenance" finding.  Modeled in ansi-c/library/string.c (C23
   7.26.5.2, provenance-preserving pointer INTO the object).  NOTE:
   library additions REQUIRE matching regression/cbmc-library/<name>/
   tests or the library-check build step FAILS.  cpp17_string_find is
   CORE now.
2. EBO allocator struct-VALUE typecast: 10-line repro (string
   move-assign from temporary).  KNOWNBUG
   cpp17_string_move_assign_alloc_cast gates on the
   "warning: ignoring typecast" soundness signal.
3. unordered_set::insert: clang-GATED cvise this time -> valid
   23-liner.  Technique: g++-preprocessed libstdc++ is clang-hostile
   (~21 intrinsic errors); run cvise with gate g++-accepts AND
   clang-not-reporting-"partial specialization|explicit specialization"
   (anti-drift), then when small, DE-GNU by hand (__remove_reference /
   __integer_pack / make_integer_sequence -> recursive impls; strip
   [[..]] attrs) and finish with the FULL clang gate.  Load-bearing:
   namespace std AND the free same-named template.
4. restrict_function_pointers root: NO cvise needed -- targeted probing
   found `return {r}` into an aggregate with a non-POD member tries
   only ctor candidates (25-line KNOWNBUG
   cpp17_return_braced_aggregate_nonpod).  Non-return braced init
   works; POD member works.  Probe ladder: real-headers repro (28
   lines) -> header-free -> ingredient bisection (const/nontriviality/
   return-context).
cvise cost lesson: criterion runtime matters -- restrict_function_
pointers' 104k-line TU = 2min/eval, infeasible; manual probing beat
reduction.  Suites: cbmc-cpp green 90 skipped, unit-proofs green 4
skipped, cbmc-library memchr tests green, String*/Memory_leak* green.

## Three-KNOWNBUG fix round (2026-07-20 evening)

1. [stmt.return]/2 + [dcl.init.aggr]: braced return operands now
   aggregate-initialize via braced_return_aggregate_value in
   typecheck_return (C++20 aggregate test with #is_implicit_ctor;
   [dcl.init.list]/3.2 same-class carve-out; bases route through
   cpp_constructor's C++17 machinery).  The return path previously
   ONLY tried constructors after the single-element unwrap.
2. Injected std::__and_/__or_ fixed-arity replacements RETIRED
   (cpp_internal_additions).  They conflicted with the real
   <type_traits> definitions ([basic.def.odr]) -- resolution bound the
   injected arity-limited primary and e.g. unordered_set's _Insert
   alias default silently failed.  LESSON: header-shadowing injections
   rot once the front end learns the real construct; prefer fixing the
   evaluator.  remove_const_function_pointers.cpp now converts (68/69).
3. Soundness: value_set_dereference's offset-0 compatible-type case
   emitted a struct-to-struct VALUE typecast for struct-PREFIX matches
   (EBO base through converted pointer); boolbv havocs those.  Now
   denotes the base subobject via get_subexpression_at_offset, typecast
   fallback preserved.  Validated: cbmc CORE, cbmc-library CORE,
   cbmc-cpp, unit-proofs -- all green.
Diagnosis shortcut of the day: renaming test identifiers one at a time
(and_ -> __and_) exposed the name collision immediately; check
cpp_internal_additions when a repro only fails with libstdc++ names.
restrict_function_pointers.cpp still fails (emplace/streamsize chain)
-- future dog-food target.

## Wide dog-food sweep round (2026-07-20 late)

SWEEP: 651 files (goto-instrument, goto-symex, analyses, cprover,
goto-cc, goto-checker, goto-analyzer, pointer-analysis, solvers/**,
cpp, ansi-c, +14 small dirs), parallel xargs -P8 with 90s each --
NOTE: 90s@P8 misclassifies big TUs as TIMEOUT (all sampled timeouts
pass at 300s sequential); use 300s or sequential for final tallies.
Initial: 304 pass / 148 fail / 199 timeout.  After this round's 4
front-end fixes + strto* models: of the 148 fails, 91+ now pass; 57
genuine fails remain.

FIXES (each with header-free CORE test):
1. [expr.dynamic.cast]/5-6 cross-casts accepted; runtime check =
   nondet(null | reinterpret) (56-file group, hardness_collectort).
2. [dcl.type.elab]/[basic.scope.pdecl] ctor-parameter elaborated tags
   pre-registered before the member pass (19-file group,
   cpp_typecheck_resolve.h).  Root: ctors deferred to a SECOND pass.
3. [temp.deduct]/8 nil-typed template args -> kind-mismatch while
   candidate matching (12-file group, optional:754 __and_fn chain).
4. [dcl.init.aggr]/5 braced args: short lists pad with
   zero_initializer; #is_implicit_ctor exempted in brace_init_is_viable
   (cpp_scope.h cache[{this,...}] shape).
LIBRARY: strtoll/strtoul/strtoull modeled (found via string2int unit
proof -- std::stoll returned NONDET).  cbmc-library tests mandatory.

NEW KNOWNBUGs: cpp17_optional_requires_ctor_pair (direct-init fails +
symex crash 'assignments must be type consistent' when used -- blocks
goto_convert*.cpp); unit-proofs/string2optional (wrap_string_conversion
lambda+catch layer nondet although direct stoll verifies).

REMAINING fail groups (future targets): 5x miniBDD parse error
('const mini_bddt & u' -- parser, friend decls?); 2x @most_derived
not-an-lvalue (solver_hardness produce_report); 2x 'transform'
unknown; 2x 'cast' ambiguous; 2x value_set_dereferencet no-match;
stoll("literal") picks wstring overload (const char* -> const int*
hard error instead of user-conversion).

GIT LESSON: grep-by-message for rebase base hashes can match `fixup!`
lines -- resolve EXACT hashes first; autosquash from a fixup hash
rebases DETACHED.  Recovery: switch back to branch, rebase with exact
parent hash.

## Sweep-findings capture round (2026-07-21)

`restrict` FIXED (scanner.l conditional_keyword like _Bool; C11 6.4.1
vs [lex.key]) -- 5 miniBDD files parse; C-mode restrict unaffected;
ansi-c suite via goto-cc green (clang_target 2 fails are HEAD-
pre-existing).  NINE new KNOWNBUGs, all probed manually (no cvise
needed -- symptom-shape guessing beat reduction every time today):
virtual-base braced init (@most_derived; ofstream/ostringstream
family), static_cast ref-downcast of operator* result, ADL via
template-argument namespaces, own-private-member in braced ctor arg,
fn-to-ptr decay in nested braces, braced reference init `int &r{x}`,
raw strings with embedded quotes (lexer stops at first '"'),
std::function-of-lambda invocation havocs, stoll("literal")
narrow/wide overload hard error.
NOT bugs: satcheck_zcore unsafe_str2int (dead code, g++ rejects too);
goto-bmc api.h + sat solver headers (environmental).
STILL unlocalized (complex instantiation chains): aligned_buffer
"type has no size" family (symex_dereference, change_impact);
'cast does not uniquely resolve' + "string'" no longer reproduced
after this round's fixes (likely downstream of restrict).
LESSON: pkill -f with a pattern matching your OWN compound command
kills the shell mid-commit; pgrep first, or use exact patterns.

## Sweep-KNOWNBUG fix round (2026-07-21 late morning)

SEVEN of nine flipped to CORE (9 src commits):
1. [dcl.init.list]/3.10 single-element list -> reference binding
   (reference_initializer unwrap).
2. [lex.string] raw strings: pending-close flush must KEEP the longest
   suffix that can still start )delimiter" (`))"` and `)x)x"` shapes).
3. [class.access.general]/5 braced-arg elements typechecked at the
   CALL SITE (pre-typecheck + already_typechecked wrapper CARRYING the
   element type for matching + icst unwrap) + [over.ics.list]/8
   single-element list -> reference PARAMETER branch in fargs::match
   and implicit_typecast.
4. [expr.static.cast]/2: judge lvalue-ness of the implicitly
   dereferenced operand ([expr.call]/14) AND the cv-gate was REVERSED
   (target may ADD qualifiers).
5. [class.access.base]/5 protected/private OWN base conversions:
   base_publicly_accessible now walks access_judgment_scope too (the
   friend rule below it already did) -- killed the
   value_set_dereferencet group as a bonus.
6. [basic.lookup.argdep]/2 ADL recurses over TEMPLATE ARGUMENTS of
   associated specializations (visited-set bounded).
7. [conv.func]/1 free-function decay in the code-typed address-of
   (ID_symbol alongside ID_member).
8. [expr.prim.id.unqual] constructed-object symbol exprs marked lvalue
   in convert_initializer (fixes @most_derived writes on braced route).
9. [temp.deduct]/8 hardening: matching guard around candidate
   deduction, unguarded #sfinae_alt retry, non-type implicit_typecast
   conversion gate.
STILL KNOWNBUG: stoll("literal") (residual in alias-template
instantiation during scope guessing -- resolve_template_alias
instantiates through convert_non_template_declaration with hard
errors), std::function-of-lambda invocation, NEW
cpp17_virtual_base_ctor_member_write (ctor-body writes through `this`
with virtual base fail bounds check, both init forms, pre-existing,
= the ofstream/solver_hardness blocker).
Suites: cbmc-cpp green 91 skipped, ansi-c via goto-cc green (2
pre-existing clang_target), cbmc CORE green, unit-proofs green.

## Fix-round findings capture (2026-07-21 afternoon)

Six KNOWNBUGs filed.  Minimal: ofstream{string}->streamsize
misresolution (10 lines); stream << setw (std::_Setw inserter via
_Require chain -- probable root of with_solver_hardness's
std::function<void(solver_hardnesst&)> param collapsing to `struct
nil`); map-from-braced-pairs at() 'deallocated dynamic object' (tree
nodes; found as a side discovery).  CONTEXT-DEPENDENT (filed as
one-include / named-source TU reproducers after isolation resisted):
goto_symex_state.h (empty-arg symbol_exprt + deleted goto_statet
default ctor demanded by synthesized code -> patht sizeless ->
aligned_buffer 'type has no size' cascade); abstract_environment.cpp
(static map<irep_idt,irep_idt> braced pair routed into the COMPARATOR
param); restrict_function_pointers.cpp (emplace no-match with
irep_idt keys).  LESSON: cvise at 35-150s/eval on 40-100k-line TUs
does not converge in reasonable time (two 55-min rounds each got
~5-30% off); for context-dependent failures the named-source-file
KNOWNBUG (options line lists the real .cpp, like unit-proofs does) is
the honest fallback and keeps the tracking test faithful.
e2 (std::function<void(T&)> param + lambda in a fresh TU) MATCHES and
converts after this round's fixes -- only invocation semantics remain
broken (cpp17_std_function_lambda_call).

## Minimal-reproducer fix round (2026-07-21 evening)

FOUR fixes (4 src commits):
1. @most_derived is now a BYTE-wide c_bool -- the 1-bit boolean made
   every following member's byte offset uncomputable (member_offset
   refuses unpadded bit-field runs; front end skips add_padding on
   based classes).  Cured the ENTIRE virtual-base member-access
   family: ctor writes through `this`, ofstream construction,
   build_object_descriptor_rec symex abort.  THE root behind weeks of
   'this->x outside bounds' symptoms.
2. [expr.type.conv]/2: functional braced casts T{...} of class types
   direct-list-initialize (aggregate -> il-ctor -> ctor args) instead
   of the C compound-literal path.  Elaborate BEFORE cpp_is_pod.
3. [temp.deduct.call]/4.3 derived-to-base deduction is TRANSITIVE
   (BFS, visited set) -- iomanip inserters resolve through
   basic_iostream.
4. [dcl.init]/16.6.2: auto-deduced non-POD from a materialized
   temporary constructs via the MOVE ctor; the old bitwise
   assign + temporary destructor freed map tree nodes still
   referenced ("deallocated dynamic object" in at()).
   Scoped to statement==temporary_object: wrapping CALL results too
   regressed optional (extra copy through the _Requires ctor family).
CORE: map_braced_pairs_at, virtual_base_ctor_member_write.
LAYERED KNOWNBUGs kept: stream_setw (residual: iostream dtor chain --
ios_base::~ios_base no-body + vtable-pointer bounds in ~basic_ios);
ofstream_from_string (verifies standalone; harness timeout + same
dtor gaps).  NEW next targets: iostream destructor chain, then
ofstream flips.
Suites: cbmc-cpp green 95 skipped, unit-proofs green, cbmc CORE green.

## Capture sweep after minimal-reproducer round (2026-07-21 night)

FIX: std::ios_base ctor/dtor modeled (empty bodies via
provide_stdlib_bodies, [ios.base.cons]/1 indeterminate members /
[ios.base.callback] no registered callbacks) -- 'no body for callee
~ios_base' gone from every stream test.
NEW KNOWNBUGs: cpp11_stream_destructor_chain (9 lines; vtable-pointer
bounds in ~basic_ios through virtual-base subobject addressing;
header-free diamond passes, so the trigger is the full iostream shape)
and cpp17_base_meminit_template_param (header-free WRONG-CODE class:
base mem-init named via the template parameter silently dropped, base
stays nondet; std::move variant errors 'invalid initializer' --
isolated from goto-symex/renamed.h by include-bisecting frame.h ->
renamed.h).
TU updates: abstract_environment's map facet FIXED by the evening
round; TU now stops at a shared_ptr resolution ambiguity, and in
two-file mode SEGFAULTS (exit 139) instantiating
sharing_mapt<dstringt, shared_ptr<const abstract_objectt>> node
machinery (small_shared_n_way_ptrt::is_derived, sharing_node.h:187) --
first outright front-end crash in the inventory; isolated
sharing_mapt shapes pass.
METHOD note: include-chain bisection (frame.h beat goto_symex_state.h)
again outperformed cvise for context-heavy failures.
NEXT: base-meminit-via-template-param fix (wrong-code!), stream
destructor vtable bounds, sharing_node segfault, std_function lambda.

## KNOWNBUG fix round (2026-07-21 night)

THREE fixes:
1. WRONG-CODE fixed: explicit POD-base mem-initializers were dropped
   ENTIRELY (not just template-param-named ones!) --
   full_member_initialization's POD branch never consumed them.  Now
   lowered to slicing assignments ([class.base.init]/7); base matched
   by name or resolved type ([class.base.init]/2).  HAZARD hit: the
   speculative typecheck_type probe surfaced errors for MEMBER names
   (56 suite failures) -- must skip member names + sfinae_contextt +
   error-count restore.
2. cpp_type2name: ID_frontend_pointer references rendered via raw-irep
   fallback, SPLITTING instantiation identity (forward<int&> existed
   as `ref_signed_int` AND `reference(signedbv...)`; body on one,
   calls on the other).  Canonicalized.
3. Post-drain sweep converts half-converted SYSTEM-HEADER instances
   (eager auto-deduction conversions absorbed by candidate matching;
   methods_seen blocked re-queueing).  Stamp = #cpp_converted on the
   value, set at convert_function success.  HAZARD: unstamped
   user-code lambdas got double-converted -- restrict to system
   headers.
std_function invocation: no-body class GONE; residual = _M_manager
dispatch imprecision (unconstrained fn-ptr candidates incl.
__do_upcast; bounds failures in ~_Function_base).
stream dtor chain diagnosis: devirtualized ~basic_ios candidates run
on facet/pthread objects with unconstrained vtables -- dispatch
precision, not layout.
GIT HAZARD REPEATED: grepping log for a commit message to find a
rebase base MATCHES THE FIXUP LINE ('fixup! <msg>' contains <msg>) ->
detached-head rebase.  ALWAYS: git log --oneline | grep -v '^\w* fixup!'
or use exact hashes noted at commit time.
Suites: cbmc-cpp green 97 skipped, unit-proofs green, cbmc CORE green.

## Capture + minimization round (2026-07-22)

FIXED (suite-validated): basic_string conversion fallback misfire --
the name-keyed char*->basic_string fallback also fired for
basic_string<wchar_t> AND leaked diagnostics from its speculative ctor
call past the catch (error-count rollback now; same hazard class as
the mem-init probe!).  std::stoll("lit") CORE + new minimal CORE
cpp17_wide_string_overload_fallback.  LESSON: any speculative
typecheck under catch(...) MUST roll back the message count.

Four new minimal KNOWNBUGs distilled from TU reproducers:
- cpp17_incomplete_template_arg_decl: CBMC instantiates a
  specialization (converting its ctor!) for a mere function
  DECLARATION ([temp.inst]/1 violation); THE goto_symex_state.h
  residual (renamed.h converts clean post-POD-base fix).
- cpp17_umap_emplace_mixed_categories: 2nd emplace instantiation with
  const-lvalue args after an rvalue one -> "found no match"; needs
  user hash + unordered_set value.
- cpp11_nsdmi_braced_null_ctor: NSDMI T x{0} with {T&&, nullptr_t}
  ctor set -> bogus ambiguity; LOCAL variable with same init works
  (8-line cvise convergence).
- cpp11_auto_ref_ref_const_lvalue: auto&& r = const_lvalue deduces
  non-reference type (missing [temp.deduct.call]/3 lvalue rule).
TECHNIQUE: goto-cc -E -o preserves CBMC's exact preprocessing;
LINEMARKERS MUST BE KEPT (syshdr error-swallowing keys on file path --
stripping them surfaces unrelated errors).  clang -E output diverges
(different error paths).  Anti-drift gates again essential: reduction
#1 drifted to writable-strings extension (add -Werror=write-strings);
reduction #2 dropped inheritance (pin with grep gates).  Eval time
DROPS as file shrinks -- a 60s/eval start converges once past ~20k
lines (rounds 1-3 slow, round 4 finished to 8 lines).
NAME-SENSITIVITY DEBUGGING: when a repro resists emulation, try
RENAMING the class in the failing case -- vI (renamed) passed where vG
(basic_string) failed, pinpointing name-keyed machinery instantly.

## Five-KNOWNBUG fix round (2026-07-22 evening)

FOUR fixed, one sharpened:
1. STREAM DTOR CHAIN (the big one): NOT dispatch imprecision after
   all!  Two real roots: (a) no-body locale::locale/ios_base::_M_init/
   locale::id::_M_id havocking every stream (modeled:
   [locale.cons], [basic.ios.cons] postconditions; __try_use_facet ->
   null for unmodeled facets); (b) CONVENTION MISMATCH: virtual-
   dispatch thunks subtracted subobject offsets while
   make_ptr_typecast uses FLAT full-object pointers for virtually-
   inheriting hierarchies (it adjusts only for non-virtual MI).  The
   4ee7f8dd49 thunk adjustment was correct ONLY for the non-virtual
   case (cpp11_virtual_dispatch_mi still guards it).  Trace signature:
   this = &obj + 2^52-k (wrapped negative offset).  Header-free
   diamond (virtual bases + non-virtual base ABOVE + derived BELOW the
   join, all five layers required) reproduces; now CORE
   cpp11_virtual_base_diamond_dtor.  setw fixed too; ofstream = BMC
   scaling only.
2. auto&& from lvalue: initializer path missed [temp.deduct.call]/3;
   drop #rvalue_reference when subtype is cv-unqualified auto and
   value is lvalue.
3. NSDMI braced init: member-initializer path lacked
   [over.match.list]/1 two-phase selection (block-scope path had it);
   raw untyped lists made ALL ctor candidates tie.
4. Incomplete-arg instances: check_member_initializers now skips hard
   errors for template instances ([temp.inst]/2 -- mem-inits belong to
   the ctor DEFINITION; conversion-time recheck still catches odr-used
   invalid ones).  SPLIT: completed-later stale-instance reuse is a
   separate pre-existing defect (new KNOWNBUG
   cpp17_template_arg_completed_later; ctor variant = symex invariant
   abort).
5. umap emplace: diagnosis sharpened -- ANY second distinct
   instantiation fails (even other map types = global state);
   unbound _Tp belongs to _Select1st::__1st_type PARTIAL
   SPECIALIZATIONS failing to rebind under _Hash_code_base
   re-instantiation.  Header-free replica passes; needs hashtable
   context.  Deferred.
Suites: cbmc-cpp green (100 skipped), cbmc CORE green, unit-proofs
green.

## Post-fix capture sweep (2026-07-22 night)

Re-survey after the five-fix round PAYS: three fresh minimals, one
72-line TU replacement, two incidental discoveries.
- abstract_env: shared_ptr NSDMI ambiguity GONE (two-phase list-init
  fixed it); next layer = braced arg skipping ref-binding for
  NON-FIRST ctor reference params (cpp11_braced_arg_ref_param_second,
  header-free 30 lines; delta_view.push_back({k, v1, v2}) shape;
  first-position ref works!).
- vector<pair<T,U>>::emplace_back with non-default-constructible T
  fails ALONE (cpp17_vector_emplace_nondefault_pair, std-only) --
  constrained pair ctor evaluates hard instead of SFINAE-discard.
  Likely the umap-emplace family root; also under sharing_node's
  pair<ssa_exprt, size_t>.
- goto_symex_state.h header KNOWNBUG replaced by 72-line reduction:
  goto_statet base + vector<threadt> + DEFAULTED COPY CTOR demands
  symbol_exprt() (no default ctor) + inaccessible goto_statet().
  TECHNIQUE: greedy block-drop bisection (split on blank lines,
  g++-gate first, then cbmc-gate) converges where cvise stalls at
  80s/eval -- 43 blocks -> 6 in ~35 min.
- optional_requires_ctor_pair REGRESSION-SHAPE CHANGE: failure went
  SILENT (statement + successors dropped from main, 0 properties,
  vacuous SUCCESS).  The desc's assertion-line pattern caught it --
  vindicates the non-vacuousness rule.  Silent statement-dropping is
  itself a to-fix defect.
- template_arg_completed_later ctor variant = SIGABRT
  (symex_assign invariant) -- filed separately (..._ctor).
- abstract_env two-file SEGFAULT relocated: now in
  typecheck_member_initializer, 17 frames (real null deref, NOT stack
  overflow); PRE-EXISTING (A/B-verified against pre-NSDMI
  cpp_typecheck_code.cpp).  Needs a RelWithDebInfo build to pin.
Suites: cbmc-cpp green, 98 skipped (100 - 5 flips + 3 new KNOWNBUGs).

## First full libc++ run + compile-only guards (2026-07-23)

Dropping -X libcxx: 26 failures / 8 classes.  FIXED the crash class
(6 core dumps): __is_convertible/__is_assignable/nothrow twin
synthesized declval probes with RAW reference types -> tripped
reference_binding precondition; __is_constructible had the correct
unwrap+lvalue-mark logic ALL ALONG -- copy it ([meta.rel],
[expr.type]/1).  4 tests recovered (one also needed --object-bits).
Two NEW minimal-root KNOWNBUGs:
- cpp11_libcxx_member_alias_shadow: `using iterator = ...` inside a
  class UNRESOLVABLE iff a same-named class template is fwd-declared
  at namespace scope AND --stdlib libc++ mode (parser flavor!)  --
  plain mode fine, non-std namespace still fires.  AND the emitted
  diagnostic is SWALLOWED (VERIFICATION SUCCESSFUL anyway) -- gate
  such tests on the diagnostic text via the forbidden-pattern desc
  section.  Root of 9 vector-family tests.
- cpp20_constraint_substitution_failure: WRONG CODE -- substitution
  failure in a concept-id's argument ([temp.constr.atomic]/3) keeps
  the constrained overload viable and SELECTED.  Root of 6 cpp20
  tests.  CVISE DRIFT LESSON x2: reductions land on clang-only
  extensions (`vector<int>;` statement) or g++/clang concept
  divergences -- when the dual gate is impossible on preprocessed
  libc++ (clang builtins), pin the INSTANTIATION CONTEXT line in the
  gate and hand-validate the final artifact.
Remaining classes tagged in-place: address_arithmetic symex abort (4),
tuple _BaseT (2), __tree __pair1_ (1), ranges unary-invariant (1).
regression/cpp: goto-cc compile-only suite; added twins for the two
BMC-scaling KNOWNBUGs (ofstream_from_string, regex_match_compile) --
pattern to keep: every scaling-limited KNOWNBUG should have a
compile-only guard.  regression/cpp + ansi-c suites green (2
pre-existing clang_target failures).

## Libc++ fix round (2026-07-23)

FIVE src commits, FIFTEEN CORE flips (oldest-standard-first order).
1. By-value braced args: THIRD copy of the [over.match.list]/1
   two-phase logic (block-scope, member-init, now by-value param
   temporaries).  Mispairing signature: error names the FIRST element
   against a LATER param's type (copy-ctor selected with whole list).
2. Struct-literal rvalue-ref args: materialize via ID_temporary_object
   side effect.  CRITICAL LESSON: new_temporary/cpp_constructor
   INSIDE argument conversion re-enters overload resolution --
   crashed (SEGV follow_tag) on nested braced map pairs.  Bisect
   lesson: a batch of uncommitted changes must be bisected by
   disabling ONE AT A TIME and re-enabling; the crash pointed at the
   WRONG suspect for four rounds.
3. libc++ fast-path ('::' navigation under suppress_elaborate) missed
   MEMBER typedefs (stored as struct components, not symbols) --
   ported filter_for_named_scopes' component-following; CLANG-gated.
4. __remove_const/__remove_volatile clang builtins: full 5-file
   plumbing (irep_ids, parser.y, scanner.l clang-gated, parse.cpp,
   typecheck_type [meta.trans.cv]).
5. libc++ allocation models: __libcpp_operator_new -> ID_allocate;
   __builtin_operator_new -> __new at goto conversion; stdexcept
   ctors/dtors empty ([stdexcept]); vector::max_size constant
   ([vector.capacity]/1, [allocator.traits.members]/6).  Chain-debug
   technique: temporarily route sfinae_contextt messages to the real
   handler (CBMC_DBG) to read SWALLOWED errors -- exposed the whole
   cascade (remove_const -> atomics void/bool -> operator_new).
Remaining libc++: tuple _BaseT (2), set comparator null-ref (deeper
layer; object-bits needed in desc), cpp20 concepts class.
Emplace family diagnosis sharpened: eager conversion of pair's
CONSTRAINED default ctor ([temp.inst]/11 violation) poisons
emplace_back's candidate via pending_no_viable_call at depth 0.

## Tuple-chain round (2026-07-24)

Commit 3fa6bff4c8: __make_integer_seq + __type_pack_element (clang
builtin ALIAS TEMPLATES -- a new builtin category; intercepted in the
resolver scope-walk / resolve() respectively) + member alias templates
binding the ENCLOSING specialization's args in resolve_template_alias.
The enclosing pre-bind needed FOUR containment iterations after
regressing libstdc++ containers: non-overriding (live bindings win),
primary-instances only ([temp.spec.partial]: spec params pair with
PRIMARY args -- positional pairing binds garbage), stop at first
parameter pack (packs need build()'s machinery), and finally
CLANG-mode gate.  LESSON: template_map pre-binding is a blunt global
instrument; scope it aggressively.
PROCESS INCIDENT: probe-stripping python with multiple lazy .*? +
re.S regexes on a 9k-line file backtracked for HOURS (cancel didn't
kill the orphan; pgrep+kill by exact PID).  RULES: literal-string or
line-based edits only for probe removal; timeout on every scripting
step; check pgrep after cancels.
Tuple residual: std::get<I>(tuple&) -- pack template-id in return
type fails deduction-substitution in full libc++ context only.

## Emplace-family root pinned (2026-07-24 late)

The 'no match for emplace_back' is NOT the constrained-ctor
escalation after all: probe chain (all-templates-fail -> fargs::match
param dump) showed the candidate's own SIGNATURE homogenised --
`_Args&&...` expanded as (symbolish&&, symbolish&&) though
pack_deduced_types = {symbolish, unsigned long}.  Root: function-type
formation expands parameter packs via pack_args_map, which the
deduction records only AFTER the type is formed; the scalar
type_map[_Args] (first element, set-once by per-element
guess_template_args) fills every copy.  EARLY recording fixes it but
double-expands two-pack ctor shapes (parameter synthesis writes
positional concrete types AND pack expansion duplicates).  NEEDED: a
single expansion point.  Reverted the experiments; kept the analysis
here + in the desc.  Probing technique that cracked it: dump ALL
params of the failing candidate in fargs::match on first
no-conversion failure.

## Concepts + pack round (2026-07-24 night)

1. Trailing-pack pre-bind (committed earlier today): fixed libc++
   tuple's _BaseT typedef fully.
2. Emplace family root PINNED but unfixed: parameter-pack expansion
   in function-type formation reads pack_args_map BEFORE deduction
   records it (late recording serves return types); scalar first-
   element fills all copies.  Early recording breaks two-pack ctors
   (double expansion).  NEED: single expansion point.  Experiments
   reverted; analysis in desc.
3. [temp.constr.atomic]/3 atom classification (committed): THROW from
   typechecking a substituted concept-id atom = substitution failure
   = UNSATISFIED (candidate loses); completed-but-diagnosed = unknown
   (atom_clean gate keeps modelling gaps conservative).  Unblocked
   ALL SIX cpp20 libcxx tests past same_as; no suite regressions.
4. cpp20_constraint_substitution_failure itself: clause DROPPED AT
   PARSE -- rConditionalExpr can't parse concept TEMPLATE-IDs in
   requires-clauses ('<' as less-than, whitelist mismatch, only a
   constraint COUNT stored).  Separate parser fix needed.

## Emplace deep-dive round (2026-07-25)

Two hardenings committed ([temp.variadic]/7 pack-empty guard;
copy-not-swap in function-template registration preserving instance
bodies per [temp.mem]).  Suite green.  Emplace family NOT fixed:
- CONFIRMED mechanism pieces: (a) function-template registration
  SWAP gutted the class-instance body's member declaration (empty
  cpp_declaration observed in the instance body); (b) the type_map-
  only pack-empty test wrongly marked 2+-element packs empty; (c) the
  instantiated symbol is homogenised (this, symbolish&&, symbolish&&)
  DESPITE pack_args_map = {symbolish, ulong} at build time.
- REMAINING UNKNOWN: which parameter-expansion path inside the member
  instantiation consumes the scalar instead of the pack.  The member-
  pack expansion site in typecheck_compound_declarator sees elems=NULL
  on an EMPTY declaration; the real expansion happens elsewhere.
- PROCESS INCIDENT #2: a 'successful fix' was an artifact of the
  line-based probe STRIPPER eating real code in resolve.cpp (later
  reverted by checkout).  RULES: after stripping probes, ALWAYS git
  diff the file against the pre-probe state and re-run the target
  test before celebrating; keep probe insert/strip pairs symmetric.
Debugging index for next session: probe convert_non_template_
declaration's parameter typecheck for the member instance; the
instantiation stack at that point is instantiate_template(emplace_
back) -> convert_non_template_declaration -> typecheck_compound_type
(the class!) -> ... (frames 13-18 of the 2026-07-24 bt).

## Capture sweep (2026-07-27)

Two header-free minimals distilled:
- cpp11_type_pack_element_return: __type_pack_element in a RETURN TYPE
  fails deduction-time substitution (local typedef works; standalone
  type works).  The get<I>(tuple&) residual, finally reproduced
  header-free after several prior sessions where replicas passed --
  the missing ingredient was the builtin in the return-type position
  specifically (libc++ mode).
- cpp20_requires_clause_concept_template_id: MULTI-ARGUMENT concept
  template-id in a requires-clause dropped at parse ('<' as
  less-than); single-arg concept constraint parses fine.  This is the
  root of ALL the cpp20 *_libcxx same_as failures and of
  cpp20_constraint_substitution_failure -- they were mis-attributed
  last round to the atom-classification evaluator, but the clause
  never reaches evaluation.
Emplace homogenization: already captured
(cpp17_vector_emplace_nondefault_pair); header-free replicas of the
member-template pack path still pass (out-of-class def + default
ctor + heterogeneous pack all insufficient alone) -- the trigger
needs the full instance-reregistration path, so the existing minimal
(which does reproduce) stays the canonical capture.
Fix directions now well-scoped: (a) evaluate __type_pack_element in
return-type substitution; (b) parse concept template-ids in
requires-clauses (rConditionalExpr / the fallback token whitelist).

## Round: type_pack_element / vector_emplace / requires-clause (2026-07-27)

### Fix 1 — __type_pack_element in return-type substitution (2473105b3b)
Three gaps in the resolve() intercept: (a) count argument arrives
`ambiguous`-wrapped during return-type substitution ([temp.deduct]/5) —
unwrap + try/catch, unevaluable => substitution failure; (b) pack
expansion `Ts...` must be spliced from pack_args_map before indexing
([temp.variadic]/5); (c) nil-typed expression-flavoured selection =>
throw 0, not invariant abort (libc++ <variant> core-dumped).

### Fix 2 — concretized pack patterns in member template instances
In typecheck_compound_declarator's pack loop, a member-template
instance's pattern `_Args&&... __args` arrives with the declaration
TYPE scalar-substituted to the first deduced element while the
declarator keeps `...` — by-name pack lookup fails and the signature
degenerates. Fallback: expand from the single live pack when NO name
in the param still spells a template parameter — gated by a new
`instantiating_member_function_template` RAII flag (ungated it fired
during CLASS instantiation and broke std::function's
_Function_handler).
LESSON (false alarm): manual `sed -n 3p test.desc` flag extraction
showed the function_basic trio failing; test.pl showed passing.
test.pl is the ONLY authority.

### Fix 3 — requires-clause concept template-ids (two commits)
(a) parse.cpp: rConditionalExpr reads `<` in `same_as<T, int>` as
less-than ([temp.names]/4), so multi-arg concept-ids lost the clause
(count-only fallback => wrong code). New rConstraintLogicalExpr
parses the restricted [temp.pre] grammar (atoms via rName which
consumes template-arg lists; !/()/bool-literals; &&/|| => ID_and/or
tree) tried before the general parser. TRAILING requires-clauses
([dcl.decl.general]/4) were skipped entirely: parse them the same
way; NB rDeclarator REBUILDS the declarator from scratch at the end
(`declarator=cpp_declaratort()`), so carry the clause in a local and
attach post-assembly. Satisfaction check conjoins head+trailing
clauses ([temp.constr.decl]/3).
(b) cpp_typecheck_resolve.cpp: same-signature twins differing only in
constraints share one symbol + #sfinae_alt; the alt was only tried on
deduction failure, so requires-rejection of the primary left ZERO
candidates and the statement was silently dropped. On requires
rejection, append the alt to the (local) work list — loop converted
to index-based to allow appending.

### Residual — cpp20_constraint_substitution_failure (KNOWNBUG)
Clause parses, constrained candidate correctly rejected; but the
half-instantiated concept-variable instance left by the GENUINE
substitution failure (same_as<int, common_reference_t<int,int>>)
poisons the second resolution pass => statement dropped (vacuous
SUCCESS caught by desc). Same family as
cpp17_optional_requires_ctor_pair. Root cause to chase: symbol-table
cleanup after throwing concept-variable instantiation.

## Round: minimal KNOWNBUG reproducers for the backlog (2026-07-28)

Seven new minimal KNOWNBUG dirs (all runtime-verified; valgrind gate
added to wrong-code reductions after an uninitialized-read
degeneration incident):
- cpp17_function_handler_dispatch (std::function dispatch, 15 lines)
- cpp11_tuple_leaf_no_body (bodies lost via __make_integer_seq /
  __type_pack_element; gates 4 tuple descs + set_insert family)
- cpp20_optional_base_alias_unknown (dependent-base alias unresolved;
  gates map_basic)
- cpp20_views_take_call_crash (single views::take call; malformed
  explicit-typecast, nil type + 2 nil operands, in
  operator_is_overloaded via guess_function_template_args; MASKS all
  preprocessed-libc++ reductions)
- cpp17_hashtable_alias_default_arg (emplace increment lost through
  alias template with computed bool-NTTP default)
- cpp17_anon_struct_member_ctor_only (anonymous-struct member of
  ctor-only type demands a default ctor; from goto_symex_state)
- cpp17_pack_cast_tuple_element_segv (functional cast to dependent
  tuple_element type with 2-arg pack; raw SEGV; from
  abstract_environment_tu; same family as views_take)

Reduction lessons:
- cvise + crash signatures on preprocessed source can be ENV-FLAKY
  (cvra: archived variants stopped reproducing outside cvise; env
  size shifts behavior).  Variant bisection against real headers
  (deterministic internal path) beat cvise there.
- Wrong-code interestingness MUST exclude UB: valgrind -q
  --error-exitcode=99 on the g++ -g binary (a reduction replaced the
  bug with an uninitialized read that "passed" runtime by luck).
- Self-archiving test.sh (snapshot first, evaluate the snapshot,
  archive on success) survives cvise state-loss on SIGINT/timeout.
- kill cvise instances via /proc/PID/cwd matching, NEVER pkill -f
  with a pattern that appears in your own command line.
- restrict_function_pointers_tu front end is FIXED (emplace fix);
  bounded BMC completes, dog-food assertion passes; vector semantic
  family + erase_if now fail only in library-modeling layers.

## Round: fixing the minimal-KNOWNBUG backlog (2026-07-28, session 2)

Five KNOWNBUGs flipped to CORE (6 src commits):
1. cpp17_pack_cast_tuple_element_segv — TWO roots: (a) parse.cpp:
   typename-prefixed names are never constructor declarator-ids
   ([temp.res.general]/4); a C::C qualifier-equality rule was tried
   first and broke libc++ iostream sentry ctors (the parser's ctor
   name representation makes pair-matching unreliable); (b)
   typecheck_member_initializer's parameter-collision path derives
   the class scope from `this` ([class.base.init]/2) instead of a
   null id_map deref.
2. cpp20_views_take_call_crash — operator_is_overloaded's
   conversion-operator branch gated to single-operand, non-nil-typed
   casts ([expr.type.conv]/2).  cpp20_ranges_basic_libcxx stops
   crashing but goes VACUOUS (silent-drop family).
3. cpp17_anon_struct_member_ctor_only — side effect of (1b).
4. cpp17_hashtable_alias_default_arg — resolve()'s alias branch now
   elaborates struct_tag results ([class.mem.general]/26 +
   [temp.inst]/2).  KEY INSIGHT: cpp_is_pod judged the enclosing
   class POD against the INCOMPLETE alias-named member class, so no
   implicit ctor was synthesized and the object stayed nondet.
   Minimal pair: member `H<int> h;` works, `ht<int> h;` fails.
5. cpp20_constraint_substitution_failure — [expr.type.conv]/1:
   functional casts T(x) with T a REFERENCE type get a synthesized
   single-argument pod-constructor (no 0-arg form, [dcl.init.ref]).
   Root shared with std::function::operator()'s
   `_ArgTypes(__args)...`.

Partial/documented:
- cpp11_tuple_leaf_no_body: 4 layers fixed (commit "bind a partial
  specialization's deduced parameters for members"):
  #spec_template_packs persistence + replay; scalar non-type pack
  member substitution; empty-pack tta expansion (CLANG-gated).
  Residual: member ctor template deduction vs concretized 3-pack
  pattern (emplace family).
- cpp17_function_handler_dispatch: reference-cast layer fixed;
  residual: `_ArgTypes(__args)...` over the replicated FUNCTION
  parameter pack arrives with an empty argument list.
- cpp17_template_arg_completed_later: staleness-remark approach
  (#had_incomplete_arg + re-elaboration) implemented and REVERTED:
  re-instantiation never rebuilds the BASE list (bases()=0) -- the
  template's stored declaration loses the base clause after first
  instantiation.  Fix needs body/base preservation first.
- Silent-drop family (ranges/optional_base/optional_requires):
  optional_base's drop chases to a nested trait-alias
  (`add_rref_t<T>` = __add_rvalue_reference(T)) instantiation
  failing inside a computed default argument during member-alias
  processing (p7 minimal pair recorded in findings; the
  ID_add_rvalue_reference typecheck branch is never reached).

Suites: cbmc-cpp green (24 skipped, down from 29), cbmc CORE green.
Lessons: test.pl/test.out is the ONLY pass/fail authority (two more
manual-grep false alarms); ungating CLANG-gated paths regresses
libstdc++ (twice this round); bisect-by-file-checkout with a 5-test
sample is the fastest regression isolator.

## Round: minimal KNOWNBUGs for the fix-round residuals (2026-07-29)

Five new minimal KNOWNBUG dirs (suite green, 29 skipped = 24 + 5 new):
- cpp11_two_pack_ctor_delegation: two-pack member ctor template fails
  deduction ONLY when called from another ctor template's mem-init
  delegation (direct call recovers).  tuple_leaf/emplace remaining
  layer, header-free ~20 lines.
- cpp17_pack_cast_fn_type_spec: pack-expanded functional cast
  `Args(args)...` in a FUNCTION-TYPE partial spec member drops the
  body; plain variadic form works.  function_handler remaining layer,
  13 lines.
- cpp20_trait_alias_default_meminit: alias-of-clang-builtin-trait
  inside a computed default template argument breaks a later class's
  member-typedef mem-initializer ("__base unknown").  Root of the
  silent-drop family (optional machinery).
- cpp17_nested_out_of_line_ctor: Outer<T>::sentry::sentry defined out
  of line never attaches (libc++ ostream sentry shape).
- cpp20_extern_template_copy_ctor_abort: cvise 73k->30 lines; an
  extern-template-declared copy ctor + a ctor taking an alias of a
  nested incomplete class chain (clang __remove_reference_t default)
  aborts typecheck_method_application on copy-ctor use.  THE crash
  masking all preprocessed-libc++ reductions.  Polished from cvise's
  self-init degenerate; explicit instantiation added so it links and
  runs clean under clang+++valgrind.

Triage updates: ranges' silent drop is an escaping implicit_typecast
in the range-for (distinct root, reduction blocked on the crash
above); map_basic's __null_state_ = trait-alias-default family.
cvise ops: dropping stability runs 3->2 and cbmc timeout 90->45s
doubled throughput; the multi-hour slow phase is
remove-unused-function on 20k+ line files, token passes then collapse
quickly.

## Round: fix round 3 over the residual minimal KNOWNBUGs (2026-07-30)

Six KNOWNBUG->CORE flips (4 src commits):
1. cpp11_two_pack_ctor_delegation: guess_function_template_args'
   post-instantiation pack expansion sized the function pack as
   args-minus-non-pack-params, lumping MULTIPLE template packs
   together -> spurious extra parameter -> unbindable.  Fix: subtract
   leading packs' deduction-time arities (#deduced_packs replay);
   unknown arity => skip.  [temp.variadic]/4-5.
2. cpp17_nested_out_of_line_ctor: typecheck_class_template_member had
   no shape case for name<targs>::name::name (out-of-line member of a
   NESTED class of a class template) -- silent return dropped the
   definition.  16-line shape branch.  [temp.mem]+[class.nest].
3. cpp17_pack_cast_fn_type_spec (+4. cpp17_function_handler_dispatch):
   make_constructors now converts substituted parse-form types
   (frontend_pointer) before POD/reference classification, so the
   pack element int& behind `Args(args)...` gets its
   [expr.type.conv]/1 candidate.  The dispatch test also had a
   GENUINE null-functor bug that CBMC then correctly diagnosed --
   repaired with real static storage (lambdas are not
   default-constructible; switched to a functor struct).
5.+6. cpp20_extern_template_copy_ctor_abort +
   cpp20_trait_alias_default_meminit: MODE ARTIFACT -- the clang
   builtins (__remove_reference_t, __add_rvalue_reference) lex only
   under --stdlib libc++ (scanner gate: CLANG mode || gcc14_builtins);
   under plain --cpp20 they parse as identifiers and fail resolution.
   Both verify with the right flags; flipped to CORE libcxx.  The
   ctor-temporary path additionally hardened: get_component's result
   is now CHECKED (was: swap empty expr -> abort
   typecheck_method_application; now: recoverable diagnostic,
   [temp.inst]/17).

BIG unblocking: the preprocessed-libc++ "masking crash" was the same
mode artifact -- re-fed preprocessed source WITH --stdlib libc++
reproduces semantic failures directly.  Vector-family reduction
running (cvv2, wrong-code + valgrind gate, CLANG-mode flags).
LESSON: reduction harnesses must carry the ORIGINAL test's mode
flags; a --cpp20-only harness on libc++-preprocessed source chases
builtin-availability ghosts.

Sweep: optional_base/optional_requires still VACUOUS in both modes
(distinct drop roots); map_basic still __null_state_; umap/tuple
libc++ layers unchanged.  cbmc CORE green; cbmc-cpp green 23 skipped
(29 -> 23).

## Round 4: empty packs in variable templates + candidate hygiene (2026-07-30)

Src commit "cpp: empty pack lists in variable templates; drop
nil-param artifacts":
- [temp.variadic]/7: `__and_v<>` (explicit empty argument list for a
  variadic variable template) left an `unassigned` placeholder that
  instantiate_template rejected; every _Requires<>-constrained
  constructor deduction failed, and with class-typed arguments the
  enclosing function was silently dropped.  Normalized to the
  empty_typet sentinel in the variable-template resolve branch.
- [over.match.funcs]/1+[temp.deduct]/8: nil-param half-substituted
  artifacts (`optionalish(? &&)`) are now rejected from candidacy.
- The zero-length-expansion fallback is precision-gated (no live
  scalar binding for the matched names) instead of CLANG-mode-gated.

Result: the optional_requires direct-init facet works in reduced form
(r3/r7/r9/r10 all non-vacuous SUCCESS); the residual layer is the
ALIAS-WITH-DEFAULTED-PARAMETER expansion `__enable_if_t<_Bn::value>...`
-- minimal pair committed as cpp17_alias_default_pack_expansion
(direct spelling works, alias spelling drops main).  A same-shape
variant (r12) hits a PRE-EXISTING symex_assign type-inconsistency
(initializer_list assigned to a struct) -- the desc's second facet.

Parked with notes: tuple_leaf CLANG-mode divergence (pack-arity fixup
computes correctly, npacks=3 lead=2, but the rebuilt instance is
rejected by the second disambiguation); optional_base's reduced file
is partially cvise-degenerate (bare `enable_if_t = 0` NTTP) -- the
real family target is map_basic's __null_state_, which needs its own
reduction (hand probes u1/u2 with layered anon-union bases pass).
Ranges' silent drop needs a reduction too (unblocked now).
cvv2 vector reduction still grinding (658KB).

## Round 4 addendum: the vector family root (2026-07-30 late)

cvv2 harvest (73k -> 18 lines, ~20h with the valgrind-gated harness;
dropping cbmc stability 2->1 tripled throughput in the token phase):
the whole vector push_back semantic family reduced to a DECLARED-ONLY
std::move.  clang's builtin std-move treatment makes the program
link and behave as the [forward]/4 cast; CBMC modelled the bodyless
instance as an unconstrained call (returned reference NULL,
moved-through values nondet).  Fix: provide_stdlib_bodies synthesizes
the return-cast body for declared-only std::move/std::forward
(prefix match: instance base names carry the template suffix).
cpp20_bodyless_std_move committed and CORE.  The four gated library
tests still fail on FURTHER layers (__end_/__begin_ unconstrained) --
re-reduce from current state next round (the established
fix-a-layer/re-reduce loop).

## Round 5: vector-family re-reduction, four fixes (2026-08-01)

Iterative fix-a-layer/re-reduce on the push_back probe (cvv3..cvv6).
Reduction lessons: the "one size: FAILURE" criterion escapes into
sanitizer-invisible UB (cross-object `&a - &b`, null-pointer
arithmetic) -- ASan/UBSan/valgrind all miss it; structural skeleton
gates (member-call spellings kept by grep) hold the shape instead.
ASan and valgrind cannot share one binary (valgrind chokes on ASan
runtime): build twice.

Layers fixed (each: cvise + hand bisection to header-free minimal,
src commit + CORE test):
1. auto-returning static members of class-template instances
   ([dcl.spec.auto.general]/13): queued conversion left `auto` visible
   to the call site; now converted eagerly under the method's map.
   Non-template classes keep the queue (cpp14_auto_member regressed on
   the first attempt -- gate on is_template_instance).
2. decltype(*p) is T& ([dcl.type.decltype]/1.5): only implicit
   dereferences preserved the reference; libc++'s iter_reference_t
   collapsed to a value type ("'operator*' not an lvalue").
3. explicit template args survive deduction ([temp.arg.explicit]/2):
   gfl pre-populated the map but the per-arg deduction pass overwrote
   it (get<W>(1,2) re-deduced T=int); re-assert after deduction.
4. C++20 parenthesized aggregate init + CTAD
   ([dcl.init.general]/16.6.2.2): pair(a, b) in make_pair; multi-op
   explicit-ctor-call reshaped into an initializer_list operand for
   ctor-less aggregates.

Diagnosis pattern that found layers 1+: the system-header leniency
(convert_function catch -> make_nil, no warning when the repair path
is engaged) hides EVERY failure in this family; the throw@__LINE__
saturation probe over resolve() + the qual-fail probe located the
silent SFINAE throws quickly.

Open root (KNOWNBUG cpp20_recursive_member_alias_base): a
base-specifier naming a RECURSIVE member alias template (_OrImpl's
`_Result = _OrImpl<sizeof...(_Rest)>::template _Result<_First>`)
resolves to `empty`; typecheck_compound_bases drops the base
(bases()=0) and qualified uses inside template bodies then no-body
their instances.  Non-recursive member aliases work (q14).  This is
libc++'s _Or/_And metaprogram -- likely also behind other libcxx
families.  uam standalone (direct __uninitialized_allocator_move call)
still fails on the same_as/common_reference chain, gated by this.

## Suite-coverage correction (2026-08-02)

User pointed out the C++ regression net is FIVE suites:
regression/cpp (goto-cc -e), regression/systemc (cbmc
--validate-goto-model --validate-ssa-equation -e),
regression/contracts-cpp-dfcc (chain.sh: goto-cc+goto-instrument+cbmc),
regression/cbmc-cpp, and regression/cbmc for sanity.  Only the last
two had been running.  Standard commands:
  cd regression/cpp    && ../test.pl -e -p -c ../../../build/bin/goto-cc
  cd regression/systemc && ../test.pl -e -p -c "../../../build/bin/cbmc --validate-goto-model --validate-ssa-equation"
  cd regression/contracts-cpp-dfcc && ../test.pl -e -p -c "../chain.sh <goto-cc> <goto-instrument> <cbmc> false true"
(goto-instrument must be BUILT -- a missing binary shows up as every
chain test failing with EXIT=127, which mimics a regression.)

Sweep results: cpp had ONE failure (base_init_pod1, predates recent
rounds -- verified with a worktree build at the round-4 tip); FIXED:
[class.base.init]/7 braced POD-base mem-initializers now
aggregate-initialize member-wise with [dcl.init.list]/3.2 same-type
copy collapse (first two attempts regressed cpp20_map_piecewise
(symex struct-arity abort) and the copy forms
(cpp11_brace_init_nonaggregate) -- the working shape routes the
operands as ONE initializer_list through explicit-constructor-call).
systemc: 5 pre-existing failures (Cast1, Masc1, Template1, Tuple1,
Tuple2; three are invariant-violation aborts) -- present at round-4
tip too; NOT yet worked.  contracts-cpp-dfcc: green.

All five suites now in the per-fix validation set (systemc failures
tracked as the known baseline until fixed).

## Round 6: minimal-KNOWNBUG fixing sweep (2026-08-02/03)

Five source fixes, each suite-validated across ALL FIVE suites
(cbmc-cpp, cbmc, cpp, systemc, contracts-cpp-dfcc):

1. systemc param invariant (5 tests, one root): unconverted member
   instances keep parse-level parameter names; clean_up now qualifies
   them ([dcl.fct]/5, [basic.scope.param]).  systemc suite green for
   the first time.
2. Three-pack ctor deduction ([temp.deduct.call]/1, [temp.variadic]/4):
   trailing-pack elements now recorded into the LAST type pack's
   argument list -- gated to >=2 template packs after the single-pack
   overwrite regressed cpp17_tuple_get_two_pack_ctor_3elem.  New CORE
   cpp11_three_pack_ctor_delegation.
3. ID_identifier preservation across the incomplete-to-complete swap
   (groundwork; the completed_later family remains parked: the
   base-specifier's template parameter does not RESOLVE at later
   points of instantiation -- three strategies failed identically;
   VACUITY CHECK caught a false "fixed" whose commit was soft-reset).
4. Zero-length pack expansion with pack_size_map-only state
   ([temp.variadic]/7): one-line gate fix; fixed BOTH
   cpp17_alias_default_pack_expansion and
   cpp17_optional_requires_ctor_pair.
5. Recursive member aliases ([temp.alias]/2): the cycle-breaker now
   keys on a binding fingerprint + scope ids and allows ONE bounded
   same-key re-entry (cap 2 -- cap 8 re-resolved exponentially and
   timed out cpp20_views_take_call_crash).  Fixed
   cpp20_recursive_member_alias_base (libc++ _Or/_And root).

Lessons: (a) the same-key re-entry through instantiate_template's
declaration conversion is LEGITIMATE, not a cycle -- binary
cycle-breaking silently empties types; (b) vacuity checks remain the
only guard against celebrating leniency-dropped mains; (c) tuple_leaf
narrows to the partial-spec base pack (leaf<T>... dropped from the
instance -- tl9 probe).

Open: ranges views::take drops main ("<<type:auto>>" conversion at
the range expression; cvv7 reduction running with the
main-dropped+vacuous criterion); tuple_leaf base pack; map_basic
__null_state_; completed_later re-elaboration.

## Round 7: parser TODOs, anon unions, harvest wave (2026-08-03)

Fixes (all five suites green after each):
1. TWO literal parser `// TODO`s from the original grammar port
   discarded pack-expansion ellipses: base-specifiers
   ([class.derived.general]) and mem-initializers ([class.base.init]).
   Base-specifier expansion implemented ([temp.variadic]/5.2,
   template-id patterns, partial-spec trailing pack recovered from
   spec_bindings) -- cpp11_tuple_leaf_no_body CORE-libcxx.  The
   arity-2 lockstep ctor case remains (cpp11_two_leaf_base_pack_
   meminit KNOWNBUG).
2. Anonymous unions with class-type variant members
   ([class.union.anon]/1 requires no member functions/static members,
   NOT POD-ness): the POD gate rejected libc++'s
   __optional_destruct_base, the map __null_state_ root.  Synthesized
   special members are exempted; re-scoping is idempotent for
   re-elaboration.  cpp20_anon_union_class_variant CORE; the variant
   MEM-INITIALIZER drop is the next layer (cpp20_anon_union_variant_
   meminit KNOWNBUG); map_basic now converts and runs BMC.
3. completed_later parked AGAIN with sharper root: the final
   completion (declaration-conversion path) runs without the template
   map; the resolve-throw recovery nils the base without re-marking.
   Durable fix: route ALL instance completions through
   instantiate_template bindings (or persist bindings on the
   instance).

Harvests:
- cvv10 (umap_emplace): reduction drifted (criterion = assertion text
  only); the original's front-end layer turned out ALREADY FIXED --
  re-scoped to the semantic-hashtable class.
- cvv9 (set_insert): 110 lines (archived .kiro/reductions); first
  distilled root = namespace-scope `T*&
  name(paren_init)` loses the pointer level ("invalid implicit
  conversion from 'void *' to 'void'") -- KNOWNBUG
  cpp11_ptr_ref_paren_init_global.  Re-reduce after fixing.
- cvv8 (map __null_state_): 11 lines -> fix 2 above.
- cvv7 (ranges): degenerated to the ill-formed `X<int>;` statement
  (clang -w accepted it; separate mini-bug: cbmc silently drops main
  on it).  Relaunched with -Werror=unused-value validity gate +
  structural greps.

Standing-rule addition: NEVER `rm -rf /tmp/cvise-*` while any cvise
runs (killed cvv7 mid-pass once; recovered from its state file).

## Round 8: four fixes, harvest continuation (2026-08-03)

1. [dcl.ambig.res]/1 vexing parse resolved by NAME LOOKUP in
   convert_non_template_declaration: a function-typed declarator whose
   "parameters" are all bare non-type names becomes a variable with a
   parenthesized initializer.  Fixed the set_insert root #1
   (`void *&child(__left_);` — pointer level lost) AND silently-wrong
   `int &r(x);` globals.  cpp11_ptr_ref_paren_init_global CORE.
2. __builtin_operator_new/delete intercepted
   ([new.delete.single] via clang's documented equivalence): libc++'s
   __libcpp_operator_new IN-HEADER body (variadic forward to the
   builtin) previously failed silently ("symbol unknown") whenever it
   was used instead of the bodyless-model path.  set_insert root #2.
   cpp11_builtin_operator_new_pack CORE-libcxx.
3. Whole-mem-initializer lockstep pack expansion ([temp.variadic]/5):
   round-7 block completed with the substitution-shape fix (raw TYPE
   where a type is expected, not an exprt wrapper).
   cpp11_two_leaf_base_pack_meminit CORE.
4. Value-init vs default-init for empty mem-initializers
   ([dcl.init.general]/9 vs /7): parser marks `member()` / `member{}`
   with "#value_init"; the anonymous-union member path
   zero-initializes those and keeps the indeterminate skip for
   synthesized default-init entries.  Gotcha: already_typechecked
   wrappers have nil types and are not lvalues — build the assignment
   from the UNWRAPPED member expression.
   cpp20_anon_union_variant_meminit CORE.

Reductions: cvv9 (set_insert round 2, post root#1+#2) at ~17KB and
falling; cvv7 (ranges, stricter gates) 83k->9.4KB, relaunched.
map_basic's next layer: map::operator[] no-body (15 failures).

## Round 9: completed_later landed; hidden friends (2026-08-03/04)

1. completed_later STRUCTURAL FIX (4th attempt, working combination):
   the #dropped_incomplete_base marker carries the dropped base's
   NAME and every retry gate checks that type's COMPLETENESS (a bool
   marker looped to the template recursion limit while the base was
   still incomplete); the reset erases the instance's STALE MEMBER
   SYMBOLS (converted against the degenerate layout, silently reused
   otherwise); the completion swap builds the template map from the
   instance's recorded arguments ([temp.inst]/2); base-specifier and
   mem-initializer-id resolution consult the map FIRST for bare
   template parameters ([temp.names]/8).
   cpp17_template_arg_completed_later CORE; the _ctor variant is
   non-vacuous and abort-free but its explicit ctor still converts
   empty at the rebuild (residual layer, desc'd).
2. Friend FUNCTION templates were silently DISCARDED by
   typecheck_friend_declaration (only friend-class-templates were
   handled): libc++'s range-adaptor hidden friend operator| never
   existed, so `arr | views::take(3)` fell into C-layer arithmetic
   conversion and main was dropped.  Now converted at the enclosing
   namespace scope ([class.friend]/1, [namespace.memdef]/3).
   cpp20_hidden_friend_operator_template CORE; cvv7's 236-line
   reduction verifies; the real <ranges> header has a further layer
   (auto-conversion at the range expr), round-3 reduction running.
3. optional_base re-scoped: real <optional> now fails PRECISELY on
   the derived-to-base reference conversion through the SFINAE'd
   assign-base chain (has_value's this-adjustment) -- fresh reduction
   queued; the old degenerate reproducer to be replaced.

Fleet: cvv7 R3 (ranges), cvv9 R2 (set_insert, ~15KB), cvv11
(libcxx_tuple, fresh).

## Round 9 addendum: harvests + degeneracy lesson (2026-08-04)

- cvv11 (libcxx_tuple): 61-line harvest -> KNOWNBUG
  cpp11_nontype_base_pack: the partial spec's LEADING NON-TYPE index
  pack base (`__tuple_leaf<_Indx>...`) drops all bases (type-pack
  analogue is fixed).  A first expander extension (non-type element
  recovery) didn't fire -- the leading pack's values aren't in
  pack_expr_map/spec_bindings at base-expansion time; reverted, needs
  its own session.
- cvv9 R2 (set_insert): drifted AGAIN to the zero-size-allocation
  artifact (`long __libcpp_allocate___size;` uninitialized -> cbmc's
  NULL-deref complaint is legitimate).  R2 result archived
  (.kiro/reductions/set_insert_cvv9_r2_114lines.cpp); R3 relaunched
  with a syntactic gate rejecting bare uninitialized *size* globals.
  LESSON: wrong-code criteria need explicit anti-degeneracy gates per
  known escape (uninit size, cross-object arithmetic, ill-formed
  statements) -- collect these in the harness template.

## Round 10: tuple root, completed_later completed (2026-08-04)

1. cpp11_nontype_base_pack FIXED (CORE-libcxx): the spec-pattern
   re-deduction admits EMPTY trailing packs
   ([temp.spec.partial.match]/2 -- equal-count guard skipped the whole
   deduction, so the LEADING index pack was never recorded), and the
   base expander handles every bound pack including non-type VALUE
   packs ([temp.variadic]/5.2).  The tuple library tests advance from
   silent wrong-code to a visible next layer (tuple_element/'get'
   resolution) -- re-reduce next.
2. completed_later_ctor FIXED (CORE): the round-9 reset had TWO
   defects -- the "tag-" strip used rfind and matched inside template
   args (stale members silently survived), and erasing members left
   dangling pointers in the method-body drain queue (SIGSEGV).
   Angle-aware component strip + queue purge BEFORE removal.  Both
   completed_later tests now CORE non-vacuous.
3. set_insert reduction parked after a THIRD degeneracy class
   (uninitialized-local-pointer, valgrind-lucky); next attempt should
   use -ftrivial-auto-var-init=pattern on the runtime gate or a pure
   value-loss criterion.
4. Ranges: cvv7 stabilized at a 236-line LOCAL MINIMUM (every line
   load-bearing; hand sub-shapes pass) -- committed as KNOWNBUG
   cpp20_ranges_pipe_invoke_drop (the invoke_result_t chain drops
   main).  Precise reproducer for its own session.

## Round 11: three walls down (2026-08-04)

1. optional_base (cpp20_optional_base_alias_unknown CORE-libcxx): the
   same-signature member-template collision branches in
   convert_function_template returned WITHOUT registering the template
   scope as a secondary scope (only the #sfinae_alt twin branch did),
   so the ctor pass's typecheck of a dependent NTTP type
   (enable_if_t<_Up::...>) failed "symbol '_Up' is unknown" and the
   whole instantiation was silently abandoned ([temp.inst]/2,
   [temp.local]).  Also: __add_rvalue_reference et al. are
   CLANG/gcc14-gated in scanner.l -- builtin-alias tests need
   --stdlib libc++.
2. tuple 'get' (cpp11_fwd_decl_template_overload CORE, apply_basic
   converts): same_template_signature (the pure-declaration ->
   definition redirect) ignored pack-ness + NTTP declared types
   ([temp.over.link]/6) and redirected libc++'s by-index get
   declaration to an unrelated same-arity overload -- the instance
   lost its parameter list.  5-line cvise harvest.
3. same_as wall (cpp20_concept_id_substitution_failure CORE): concepts
   lower to constexpr bool variable templates with no concept marker;
   a concept-id whose argument substitution is invalid must evaluate
   FALSE ([temp.names]/9, [temp.constr.atomic]/3) but hard-errored.
   Parser '#concept' marker + SFINAE-guarded resolve folding to false
   (expr site + both initializer conversion sites).  The ENTIRE
   vector/map/initializer_list/erase_if family now converts; next
   layers are semantic (vector size() pointer-diff checks, map
   operator[] no-body, construct_at derefs, initializer_list
   wrong-code, erase_if scale).
   NOTE: flipping the spec-selection requires-clause catch(...) to
   unsatisfied per the same clause REGRESSES cpp20_concepts_ordering
   (trait-based clauses whose EVALUATOR fails, not substitution) --
   reverted; the targeted concept-id fix suffices.
4. cvise on rejection signatures is extremely effective: cvt1 466KB ->
   149 B in ~40 min; cvt2 2.7MB -> 1.9KB.  Both roots fixed same-day.

## Round 11 addendum: __bind_back_op triple (2026-08-04)

cpp20_nontype_pack_spec_multi CORE-libcxx -- three coordinated fixes
for the ranges-pipe invoke chain's __bind_back_op shape:
1. [temp.param]/14: preceding EXPRESSION parameters now bind before a
   default template-argument is materialized (type params already did).
2. [intseq.make]: bare (unqualified-use) __make_integer_seq intercepted
   at resolve() entry, expanding to Tpl<T, 0..N-1> (the resolve_scope
   intercept only covered qualified uses).
3. [temp.variadic]/5: a template-argument pack expansion whose pattern
   is a BARE non-type pack reference now emits the pack's i-th VALUE
   (apply() only rewrites type names; the scalar convenience entry --
   the first value -- leaked into every element, `<ul,0,0>` vs
   `<ul,0,1>`, spec never matched).  Also spliced pack_expr_map in the
   fn-template guessed-args expansion.
COST: <functional> now converts FULLY; the std::function smoke tests
(cpp11_function_basic_libcxx, cpp17_functional_basic_libcxx) exceed
900s in the SAT solver and moved CORE -> THOROUGH (scale, documented).
ranges_pipe next layer: implicit_typecast throw inside alias template
args during elaborate_class_template (fresh diagnosis needed).

## Round 11 addendum 2: get redirect, third shape (2026-08-04)

same_template_signature now compares parameter TYPES with two
normalizations ([dcl.fct]/5 names erased; own template params renamed
positionally per [temp.over.link]/6).  CAUTION captured: comparing
WITHOUT erasing names broke std::swap (unnamed decl vs named defn,
bits/move.h) -- cpp11_require_swap caught it.  Tuple family now runs
BMC end-to-end; next layer: get's DEFINITION body not instantiated at
the call (no-body FAILUREs; apply_basic vacuous-success, props=0).
cvt1 relaunch for layer 4 uses criterion "no body for callee
std::__1::get".

## Round 12: reduction launches + two bootstrap fixes (2026-08-05)

Launched cvu1 (tuple, criterion "no body for callee std::__1::get",
seed preprocessed cpp11_tuple_basic 466KB, ~240s/iteration with clang
pre-gate; 40000s budget).  vector/map harnesses (criteria: "same
object violation in this->__end_ - this->__begin_: FAILURE" resp.
"in \*return_value_operator\[\]: FAILURE", both with clang gate;
vector also ASan/UBSan runtime-clean gate) are WRITTEN but seeding is
parked: re-parsed preprocessed source loses system-header leniency
and surfaces a chain of real front-end gaps:
1. FIXED: constexpr arrays folded to literals (address_of error on
   &__digits_base_10[i], <charconv>) -- two-part fix (declarator
   converter keeps is_macro false => static init; resolver keeps
   symbol expr), CORE cpp17_constexpr_array_element_addr.  First
   attempt kept the symbol but lost initialization -- assertion
   caught it (value was nondet).
2. FIXED: ADL ignored ENUM arguments ([basic.lookup.argdep]/2.3) --
   libc++ poison-pill make_error_code found only the deleted pill.
   CORE cpp20_adl_enum_poison_pill.
3. Seed-local stubs (not bugs to fix now): pthread mutex/condvar
   NSDMI union braces, `restrict` params (wcsnrtombs), and
   __uninitialized_allocator_move_if_noexcept bodies.
4. NEXT (unfixed): basic_string<int> union-rep members __is_long_/
   __size_/__cap_ unknown in __get_short_size/__get_long_cap when
   re-parsed outside system headers.
Seed recipe recorded: cbmc --preprocess | grep -v '^#', prepend
__CPROVER_assert decl, apply stubs 3.

## Round 12 addendum: cvu1 relaunch (2026-08-05)

First cvu1 run finished in ~1h but DEGENERATE: cvise deleted get's
DEFINITION, making "no body for callee std::__1::get" trivially true
(a bodiless declaration correctly yields no-body -- not the bug).
LESSON: no-body criteria need a definition-must-survive anchor, same
family as wrong-code anti-degeneracy gates.  Relaunched with
`grep __tuple_leaf` + `grep 'get\(tuple<_Tp\.\.\.>&'` anchors.

## Round 13: packed rep + ranges scoping (2026-08-05)

1. cpp11_packed_anon_struct_member CORE: GNU-attributed member class
   definitions -- rGCCAttribute's merge_types wrapped the struct and
   rClassSpec attached TAG+BODY to the WRAPPER (bodyless struct
   downstream).  Parser unwrap after optAttribute (mirrors the alignas
   unwrap; packed -> ID_C_packed) + 3 typecheck hardenings
   (is_anonymous survives the bodyless conversion AND the completion
   swap; anon-member injection looks up by TAG identifier, ID_name may
   be absent post-swap).  Unblocks the vector/map reduction seed
   recipe (basic_string's rep bitfields resolve).
2. ranges_pipe scoped to its true next layer: the itc-throw shape
   (1382B archive) passes in direct forms; the faithful
   inheriting-ctor form crosses the front end and crashes SYMEX
   (goto_symex.cpp:80 type mismatch) -- banked
   cpp20_inherited_ctor_symex_crash KNOWNBUG.
3. LESSON: probe-based cvise criteria die when the probe is stripped
   -- archive the reduction BEFORE removing probes, or key the
   criterion on shippable output only.

## Round 14: symex crash fixed + validation discipline correction (2026-08-05)

1. cpp20_inherited_ctor_symex_crash CORE-libcxx: the partial-spec
   pattern re-deduction recorded pack bindings only on the instance
   symbol; the class body then converted with an EMPTY pack map, the
   sizeof...-based static member initializer failed inside the SFINAE
   guard, and the RAW parse tree became the member's value (malformed
   goto assign -> symex invariant).  Fix: record EMPTY packs too and
   REPLAY all spec_bindings into the active map before body conversion
   ([temp.inst]/2, [temp.variadic]/7,/8).
2. CRITICAL PROCESS BUG FOUND: regression/cpp, systemc and
   contracts-cpp-dfcc validations had been running a STALE goto-cc /
   goto-instrument for several rounds (only the cbmc target was
   rebuilt).  A round-8 regression (constexpr scalar paren-init
   through the [dcl.ambig.res]/1 disambiguation leaving a VOID value:
   most_vexing_parse) was masked the whole time.  Fixed
   ([dcl.init.general]/16.9 single paren initializer becomes the
   symbol value, mirroring the reference case), CORE
   cpp11_constexpr_enum_paren_init.  RULE: rebuild cbmc goto-cc
   goto-instrument before every suite validation.
3. __make_unsigned/__make_signed clang builtins modelled
   ([meta.trans.sign]) -- CORE cpp11_make_unsigned_builtin; unblocks
   the <vector> seed past __half_positive.
4. vector seed's NEXT blocker: "symbol '__s' is unknown" in
   basic_string<char> anon-union rep, triggered by the extern-template
   explicit-instantiation declarations (two-instantiation shape passes
   in isolation; needs the extern-template ingredient).

## Round 15: friend-template unification (2026-08-05)

1. cpp11_friend_template_definition_body CORE: [temp.over.link]/6 --
   an in-class friend fn-template declaration and its namespace-scope
   definition (different parameter SPELLINGS) declared TWO symbols;
   calls hit the bodiless friend ("no body for callee get", the
   <tuple> access family), and the definition's body failed the
   private-member access check.  Fixes: signature unification in
   convert_function_template (equivalence per [temp.over.link]/6-7 +
   [defns.signature.templ] INCLUDING return type, method
   cv-qualifiers, constraints -- two suite regressions caught during
   development: std::_Any_data's const/non-const _M_access pair, and
   the concept-subsumption overloads); friend fn-templates recorded in
   C_friends ([class.friend]/1); access check accepts specializations
   via ID_C_template ([temp.friend]/1).
2. cvu1 harvested (66 lines): the REMAINING tuple layer is a
   non-friend get whose RETURN TYPE resolves through the recursive
   tuple_element/__make_tuple_types_flat machinery -- instance comes
   out bodiless.  KNOWNBUG cpp11_tuple_get_return_type_body (leaf-ctor
   value propagation restored; cvise's driver was degenerate
   self-referential).  tuple_basic's next visible layer: the tuple
   CONSTRUCTOR no-body.  apply_basic reaches VERIFICATION SUCCESSFUL
   (vacuity unverified this round).
3. ranges_pipe: 218/236 lines load-bearing under the fatal-outcome
   criterion; nil-index_sequence throws during spec selection are
   RECOVERABLE; the fatal layer is deeper (silent resolve failure in
   guess_function_template_args); needs a throw-index bisection
   harness.
4. cvs1 (__s layer) still reducing (~1MB of 2.7MB).

## Round 16: multi-pack absorption + lockstep values (2026-08-06)

cpp11_tuple_get_return_type_body CORE-libcxx.  Two roots:
1. [temp.spec.partial.match]/2: multi-pack spec patterns
   (__tuple_impl's <size_t... _Indx, class... _Tp>) with npat < nfull
   FLAT argument lists were rejected at BOTH matching sites (selection
   loop + spec_bindings re-deduction) -- no __tuple_leaf bases, get's
   derived-to-base static_cast threw inside the drain, get left
   bodiless.  Fix: positional prefix + remainder bound as ONE pack,
   STRICTLY gated to heads with >= 2 packs (single-pack double-binding
   regressed cpp11_variadic_ctor_pack_multi and
   cpp11_recursive_forwarding_tuple_ctor -- suite caught both).
2. [temp.variadic]/5: the whole-mem-initializer lockstep expansion now
   substitutes NON-TYPE pack element VALUES (elem_expr_by_short) --
   `__tuple_leaf<_Uf>(__u)...` previously sent every element to
   __tuple_leaf<0>.
LESSONS: (a) several regression tests EXPECT VERIFICATION FAILED (a
"WRONG must FAIL" assertion) -- diagnose by SPECIFIC assertion labels,
never by exit status or tail; (b) after any stash/pop cycle REBUILD
before concluding anything (a stale binary re-misled the bisection
mid-round).
Tuple family's remaining layer: the tuple CONSTRUCTOR no-body
(_EnableUTypesCtor enable-if machinery).

## Round 16 addendum: lambda trailing decltype (2026-08-06)

cvs1 (the __s anon-union criterion) converged on a SHALLOWER bug
satisfying the same message: lambda parameters not in scope in their
own trailing return type ([dcl.fct]/8), doubly broken (pre-scope
typecheck + raw parse tree re-typechecked in the closure class).
Fixed; CORE cpp11_lambda_param_trailing_decltype.  The anon-union __s
layer itself remains unharvested -- reseed with a criterion EXCLUDING
the lambda shape (e.g. require "__rep" or "basic_string" to survive)
next time.

## Round 17 (2026-08-06): tuple_size triple fix; host OOM lesson

Tuple ctor no-body root #1 FIXED (three defects, one commit):
strict cv deduction in partial-spec matching ([temp.deduct.type]/8,
opt-in flag set at the 3 matching sites); cv-qualified alias-argument
substitution ([temp.alias]/2); pack ELEMENT substitution in
template-arg expansion ([temp.variadic]/5 -- bare cpp_names were left
textual and re-resolved against the PRIMARY's same-named param).
tuple_size<tuple<int,int>> now correct and fast (was wrong + ~5min).
CORE: cpp11_tuple_size_alias_spec (27-line header-free).

Tuple ctor next layer (diagnosed, not fixed): __integer_sequence<
size_t,0,1>::__to_tuple_indices<0> -- template::232::_Values unbound
at a resolve INSIDE instantiate_template(convert_non_template_
declaration) nested under resolve_template_alias; the rta pre-bind
(CLANG-gated, cpp_typecheck_resolve.cpp ~4990) DID bind it, but the
map is empty again at the throw -- the inner instantiate's
convert_non_template_declaration path apparently runs after restore
or in a different map frame.  Resume: probe rta-enter parent + map
state inside frame #4 (instantiate_template) of the saved bt.

Diagnosis recipe that worked: global `bool cbmc_dbg_in_target` set in
convert_function for the target symbol; gdb `break __cxa_throw if
cbmc_dbg_in_target` + ignore-count bisection; swallow-site probes in
method_bodies/convert_function (cf-catch/cf-nobody found the recovery
path; error stream at catch holds ONLY instantiation context -- the
message itself goes to the nulled handler).

OPS LESSON (host died, /tmp lost): 3 cvise jobs x 5 workers x 6GB
cbmc caps ~ 90GB worst case on a 68GB host.  Budget the FLEET, not
just each process: at most ONE cvise with --n 4 (4x6=24GB) alongside
interactive work, or cap per-run ulimit so total_workers x cap <
RAM/2.  Reduction jobs lost (cw1 tuple-ctor link+run gate; cw2
<<type:auto>> decay_t criterion; cw3 __pair1_/__node_holder criterion
with = {} pthread stubs -- NOT plain removal, which breaks constexpr
mutex() natively).  cw1 is now OBSOLETE (this fix reached deeper via
direct diagnosis); cw2/cw3 recipes recorded above for relaunch.

## Round 17 cont. (2026-08-06 evening): empty-pack pre-bind; next tuple layer

FIXED: member-alias enclosing pre-bind skipped a trailing pack once
the instance's args ran out ([temp.variadic]/7 -- empty pack is still
deduced).  __integer_sequence<size_t>::__to_tuple_indices<0> threw on
unbound _Values; sequence-counter probes proved the <ul,0,1>/<ul,0>
resolutions bound fine and only the EMPTY <ul> one threw.  CORE:
cpp11_member_alias_empty_pack (counterfactually verified via
stash+rebuild).

Tuple ctor NEXT layer (evidence, not yet fixed): with the _Values
throw gone, the ctor body conversion now dies in a candidate-churn
storm -- ~39k alternating SFINAE throws on pair's 339::_T1 vs tuple's
269::_Tp during typecheck_decl of a mem-init temporary
(resolve_scope -> disambiguate __make_tuple_types -> per-candidate
typecheck).  Final throw escapes to convert_function's catch(int) with
EMPTY error stream.  Shape strongly resembles the tuple_size churn
(fixed by strict_cv_deduction) but through _CtorPredicateFromPair /
_EnableCtorFromPair (tuple:741-780, pair-taking ctor family whose
enable_if evaluates against tuple<_Tp...> with _T1/_T2 patterns).
Resume: identify why the pair-ctor candidates are instantiated at all
during a UTypes-ctor body conversion; likely another deduction
leniency (per [temp.deduct.type]/8 the pattern pair<_Up1,_Up2> cannot
match int) letting a doomed candidate substitute expensive SFINAE.
Watch total wall-time: ~5min for tc.cpp even now.

## Round 17 cont. 2: cw3 harvest fixed (incomplete-instance deduction)

cw3 converged at 835B; hand-tightened to a 23-line STRICT-C++11 repro
(the cvise output itself relied on a C++20 typename omission g++
rejects -- ALWAYS re-verify harvests with g++ -std=c++11, the clang
gate alone is too lenient).  Root: guess_template_args' template-id
branch required ID_C_template on the argument instance; a
forward-declared-only template's instance (tag-__tree_node<int,void>)
has full_template_args but no C_template -> pattern
__tree_node_types<_NodePtr, __tree_node<_Tp,_VoidPtr>> undeduced ->
declaration dropped.  Fixed by accepting recorded template arguments
([temp.deduct.type] needs no completeness).  CORE:
cpp11_spec_match_incomplete_instance.

set_insert NEXT layer: same __pair1_ as a MEMBER of __tree now fails
"invalid initializer '__pair1_'" at <__tree>:1341 (the member decl
converts, but its use in __tree's ctor mem-init region misfires).
Then the wrong-code layer (pointer derefs) behind it.

Diagnosis speed lesson: the map-dump probe at convert_template_
parameter's throw (identifier + type_map one-liner) found in ONE run
what bt-based bisection took six runs to narrow; prefer it for
'symbol X is unknown' bugs.  sizeof(empty struct)==0 in CBMC (g++: 1)
-- do not gate repro assertions on sizeof of possibly-empty structs.

## Round 18 (2026-08-06 night): SFINAE storm + five-pack ctor

FIXED (2 commits):
1. has_conflict() at the 3 candidate gates ([temp.deduct.type]/2 --
   ID_nil conflict bindings weren't rejected, doomed candidates paid a
   full throwing pattern re-typecheck each; 39k throws/400s -> 50
   throws/5.5s for tuple<int,int> ctor conversion).
2. Multi-pack function templates (__tuple_impl's 5-pack ctor;
   [temp.variadic]/5,7,8): gfta flat-args splice from per-pack
   bindings; build() keeps deduction-time bindings when all packs
   live (erasing >=2-element scalar residue -- the per-element
   deduction leaves the LAST element in type_map, which concretizes
   the pattern and defeats the in-class replication -- THAT was the
   final piece); own-pack check in BOTH copies of the empty-pack
   param removal (any-empty-pack removed the non-empty _Up&&... too).
   All gated n_packs>=2.  CORE: cpp11_multi_pack_ctor (202 = arities
   2/0/2 through a mem-init).

Instantiation-path map (hard-won; keep): plain-class member template
ctors go instantiate_template -> is_template_method(5497) ->
typecheck_compound_declarator(6083); their function-param-pack 1->N
replication lives in cpp_typecheck_compound_type.cpp ~510-720 keyed
BY NAME (pack_by_short/referenced_pack).  FREE function templates
expand at instantiate_template ~6950 (pack_arguments machinery, ALSO
patched for multi-pack).  Class-template members expand during class
instantiation (4785 branch).  A scalar type_map binding for a pack
BREAKS the name-keyed replication -- invariant: packs with >=2
elements must never have type_map/expr_map scalar entries.

Tuple next layer: __base_ call now resolves; no-body moved INTO
__tuple_impl's 5-pack ctor instance (mem-init lockstep
`__tuple_leaf<_Uf,_Tf>(std::forward<_Up>(__u))...` -- three-pack
lockstep over Uf/Tf/Up; round-16's elem_expr_by_short handles values,
likely needs the multi-pack treatment for the leaf TYPES too).

Diagnosis efficiency: counting probes keyed by base_name at
disambiguate/typecheck_template_args entries found the hot template
in ONE run; the instantiation-stack print at convert_template_
parameter's throw gave the semantic context without gdb.

## Round 19 (2026-08-07): TUPLE FAMILY COMPLETE — 4 KNOWNBUG -> CORE

std::tuple works end-to-end under libc++ (construction, get, make_tuple
heterogeneous, apply).  Final layer had three defects
([temp.variadic]/5,7):
1. mem-init pack expansion with NO function param pack
   (`leaf<Ul,Tl>()...`) — arity from template packs' common length;
   empty -> DROP the initializer (was: dangling `...` failed the ctor).
2. base-specifier expander substituted only the FIRST referenced pack
   (parallel packs collapsed to scalar -> leaf<k,int> for
   tuple<int,double,char>; homogeneous tuples masked it).
3. apply()'s base-template-args fallback + spec-matching convenience
   entries concretized >=2-element pack names before the expander.

REGRESSION LESSON (suite caught both): the deduction-side scalar
convenience entries in cpp_typecheck_resolve.cpp (4411, 7659) are
LOAD-BEARING for member-alias (cpp11_alias_template_parallel_pack) and
variable-template (cpp14_variable_template_pack_partial_spec)
machinery — blanket-gating them to single-element regressed both.
The >=2 invariant applies ONLY where name-keyed re-expansion follows
(instantiate spec-matching sites, build(), gfta); deduction-side
consumers resolve through build_template_args which needs the scalar.

Desc format gotcha: several old KNOWNBUG descs lack the second `--`;
their history notes sit in the disallowed-regex section and test.pl
FATALS on unparenthesized '(' in them once the test is CORE.  Insert
the separator when flipping.

Remaining 14 KNOWNBUGs.  Next: cx1 set member layer (1KB harvest),
cx2 (240B), cw2 (3.1KB), umap cy1 reducing.

## Round 19 cont.: cx1 root found — TT-param binds instance not template

px-chain bisection of the cx1 harvest: `R<_Alloc<_Tp>, _Up>` with body
`_Alloc<_Up>` yields allocator<int> for _Up=char — the TT param is
bound to the argument INSTANCE ([temp.deduct.type]/8 requires the
TEMPLATE).  Candidate fix (template_parameter_symbol_typet binding,
mirroring typecheck_template_args' explicit-TT representation) FIXES
the whole px chain + makes set_insert's conversion clean (only its
wrong-code layer left!) BUT regresses cpp11_libcxx_tuple (make_tuple
wrong-code returns) and pushes deque/map past 2^8 objects — instance
unification was load-bearing somewhere in make_tuple's chain.  Patch
archived (.kiro/reductions/tt_param_deduction_fix_regressed.patch);
KNOWNBUG cpp11_tt_param_rebind_instance banked.  Next attempt should
find WHERE the instance-binding is consumed (probably template_map
apply of `_Alloc<_Up>` bodies) and fix the CONSUMER instead, or
gate the template-binding to non-deduced contexts.

Empty-struct sizeof==0 artifact bit twice more in repro assertions —
use data members, never sizeof(struct)>=1.

## Round 20 (2026-08-07): cx2 + cw2 roots fixed

1. cx2 (regex divergence): [basic.lookup.unqual]/5 -- the
   [dcl.ambig.res]/1 re-disambiguation probed parameter names at
   namespace scope; out-of-line member decls need the member's class
   scope (+ [dcl.fct]/6 cv-qualifier forces function interp).  CORE
   cpp11_expl_spec_member_decl_class_lookup.  GOTCHA: cpp_declaratort::
   method_qualifier() non-const accessor add()s an empty node -- gate
   via const read or id().empty(); the non-const read silently
   disabled the whole re-disambiguation (suite caught
   cpp11_ptr_ref_paren_init_global).
2. cw2 (<<type:auto>>): [dcl.spec.auto.general]/13 -- bodiless
   `auto end(T);` outranked defined `end(T(&)[N])` via the
   template-arg-COUNT tie-breaker.  Fix: intermediate ranking key
   penalising candidates whose TEMPLATE has no body (never-deducible
   auto).  TWO failed attempts instructive: (a) binary non-template
   key + partial-ordering delegation regressed erase_if/sort (count
   key load-bearing for __copy_move stack -- old key selects the
   ITERATOR __copy_m whose pointer handling happens to verify; the
   standard-correct pick exposes a LATENT pointer bug, parked);
   (b) ret==auto penalty was a no-op (ALL not-yet-instantiated
   candidates show auto at ranking) and I nearly committed it on a
   vacuous SUCCESS -- tail -1 is NOT verification, ALWAYS check
   props>0.  CORE cpp20_undeduced_auto_overload_rank.
   cpp20 family now converts + runs BMC end-to-end (vector 9/5289
   fails = semantic layer; initializer_list memmove preconditions;
   erase_if next).
3. regex symex crash still behind a 'class template std not found'
   divergence (cx2 relaunched on that criterion); cy1 (umap) relaunched
   with VALGRIND gate (ftrivial-auto-var-init gate was gameable:
   pattern-init is nonzero natively, nondet in CBMC).

## Round 20 cont.: regex divergence layer 2 (namespace-qualified defs)

cx2 second harvest (252B, minutes to converge): out-of-line member
definitions with a redundant NAMESPACE qualifier
(`std::basic_streambuf<_T>::basic_streambuf(...) = default;` inside
namespace std, [class.mfct]/1 + [namespace.qual]) fell through the
A::B<args>::member handler (class-only leading-component lookup) and
killed the TU.  Fixed + CORE cpp11_ns_qualified_member_definition.
cx2 relaunched on regex layer 3: "found no match for symbol
'logic_error'" with EMPTY argument types (a __throw_logic_error
definition whose throw-expression's ctor args vanish).  The symex
crash criterion remains queued behind it.

## Round 21 (2026-08-07 night): TT-param CORE flip; cy1 extension-drift

FIXED + FLIPPED: cpp11_tt_param_rebind_instance KNOWNBUG->CORE.
Consumer-side rework ([temp.deduct.type]/8): a TT-parameter USE with
its own template-argument list derives the TEMPLATE from the bound
instance at the resolve-with-args site (cpp_typecheck_resolve.cpp
~5710); the deduction-side instance binding stays (its unification is
load-bearing -- the binding-site fix regressed make_tuple + object
ceiling, archived patch documents it).  px chain + set_insert
conversion advance; set's next layer: __node_allocator/__node_traits
unknown (member typedef chain, likely SAME family as the fixed rebind
-- worth a quick probe next round).  5 suites green.

cy1 (umap) harvest was INVALID C++: partial spec with fewer args than
primary = g++ extension, clang rejects ([temp.spec.partial.general]).
Distillations chased a phantom; the REAL libstdc++ shape (explicit
bool specs, uf4 control) verifies fine, so umap's root is elsewhere.
LESSON: gcc-preprocessed seeds + g++-only gates allow extension
drift; cross-preprocessing swaps one builtin gap for another
(__remove_reference vs __is_array).  Adopted gate: clang
-fsyntax-only ERROR-COUNT BASELINE (seed yields 15, all cascades of
__remove_reference/__integer_pack; reject any variant exceeding it).
cy1 relaunched with it; cx2 (logic_error empty-args) still grinding.

## Round 22 (2026-08-07 late): TT-scope fix; init_list narrowed; cx3 launched

FIXED: resolve_scope counterpart of the round-21 TT-consumer fix
([temp.deduct.type]/8) — TT-param as SCOPE component with args
(`_Alloc<_Tp,_Args...>::template rebind<_Up>`).  CORE
cpp11_tt_param_scope_rebind.  Real set_insert STILL fails
__node_allocator: full-fidelity models (nx8/nx9 incl. the SFINAE
discriminator + _Tp short-name collisions) all PASS — the residual
needs real-header context; cx3 reduction launched (criterion
'__node_allocator is unknown', clang+libc++ compile+run gate, --n 2).

initializer_list layer NARROWED: memmove preconditions GONE (round-20
fixes); the residual wrong-code is inside the
vector(initializer_list) ctor chain — the ctor IS called with a
correct {arr,3} temp; size ends wrong.  Next: --trace session on the
size assertion; suspect __init_with_size / construct_at loop under
--unwind 5.

Three reductions running (cx2 logic_error, cx3 node_allocator, cy1
umap baseline-gated), 3+2+3 workers x 4GB = 32GB budget OK.

## Round 22 cont.: harvest triage

cx3 (907B) leaned on implicit-typename (C++20-in-cpp11 clang
extension); strict models pass -> relaunched with g++ error-count
baseline gate (2125, clang-builtin cascades).  cx2 (102B) criterion
was GAMED: its 'CONVERSION ERROR' came from the harvest's own invalid
`main()` while the logic_error no-match is RECOVERED noise (the
[class.default.ctor]/2 implicit-deletion machinery works: le1/le2
strict repros verify fine, le2 even exercises throw/catch of the
derived).  Relaunched with a CAUSAL criterion (no-match within 8
lines of CONVERSION ERROR).  LESSON for criteria: pair the marker
with its consequence, not mere co-occurrence.

## Round 23 (2026-08-08): constexpr-dtor WRONG-CODE root — init_list CORE

MAJOR: cpp20_libcxx20_initializer_list KNOWNBUG->CORE.  Root was a
SOUNDNESS bug: constexpr member functions get is_macro (constexpr
evaluator candidates); C++20 constexpr DESTRUCTORS ([dcl.constexpr],
P0784) were caught too, goto conversion folded the call away, and the
dtor's SIDE EFFECTS vanished — libc++ _ConstructTransaction's commit
(`__v_.__end_ = __pos_`) never ran, so EVERY initializer-list/range
vector was silently EMPTY under --cpp20 (correct under --cpp17!).
Diagnosis: --trace showed __tx.__pos_ = +3 but no __end_ write; the
dtor SYMBOL was entirely absent from the goto (call to nonexistent
symbol = silent havoc, no 'no body' property!).  Header-free repro
ct3 (constexpr ctor+dtor in nested struct of class template, ref
member); ct4 = dtor-alone discriminant.  Fix: exclude destructors
from is_macro.  CORE cpp20_constexpr_dtor_side_effect + flip (desc
also needed --object-bits 12).

REMAINING cpp20 layer (vector_basic/libcxx20_vector/map): pointer
checks on `__end_ - __begin_` (same-object violation / overflow on
null-null? size() over default-constructed vector) — instrumentation
semantics, next session.

NOTE for symex/goto: a CALL to a symbol ABSENT from the symbol table
produces NO no-body property — silent havoc.  Worth a general
diagnostic sweep some round.

## Round 23 cont.: TT-instance family, third round of consumers

cx3-v2 harvest converged to the SAME attractor (typename-omission
drift under the loose 2125-error baseline) BUT strictifying it by
hand (adding typenames) kept the failure — harvest drift does not
always invalidate the shape; ALWAYS try strictifying before
discarding.  Root: template_map.apply substitutes a TT-instance
binding TEXTUALLY into qualified names; the scope walk then sees
`tag-allocator<signed_int>` as a template NAME.  Fixed in
disambiguate_template_classes' fallback chain (+ guards at
class_template_symbol/instantiate_template entries).  CORE
cpp11_tt_instance_tag_scope.  Real set_insert: ONE more layer —
nested own-param capture in rebind_alloc's alias body
(allocator_traits' _Tp vs allocator's _Tp, the top-level-only
#tmpl_param_shadow protection at template_map.cpp ~640; extending it
to nested refs previously warned as risky — std::function relies on
nested-capture behavior; needs a careful scoped approach).

Round-23 totals: constexpr-dtor WRONG-CODE fix (init_list CORE flip +
cpp20_constexpr_dtor_side_effect CORE), TT-instance third-consumer
fix (cpp11_tt_instance_tag_scope CORE).  13 KNOWNBUGs remain.

## Round 24 (2026-08-08): umap root pinned via goto/trace forensics

Both cx2/cy1 harvests RE-degenerated to their old attractors (gates
insufficient against these shapes) — pivoted to direct diagnosis.
umap wrong-code root PINNED: _Hashtable::_M_emplace's
`_Scoped_node __node{this, forward<_Args>(__args)...}` with a pack of
TWO CLASS-TYPE RVALUES selects the 2-param (node*, alloc*) ctor
instead of the variadic allocating one; node stays uninitialized;
duplicate check compares garbage; same-key emplace double-inserts.
Discriminants: 2 class rvalues required (1 passes, scalars pass,
braces-vs-parens irrelevant).  KNOWNBUG cpp17_scoped_node_pack_ctor
(37 lines, runtime-verified).  Forensics chain that worked: goto dump
-> only ONE pair-ctor instance (ref) -> rvalue _Scoped_node ctor body
assigns __h/__n only (2-param overload's params) -> trace shows
single .no write.  NEXT: diagnose the overload selection for the
2-class-rvalue pack (likely the pack-vs-fixed-arity candidate
ranking, cpp_typecheck_resolve disambiguation; compare with sn1-sn3
passing variants).

## Round 24 cont.: umap ctor no-body narrowed further

The wrong-SELECTION theory was wrong: the CALL targets the CORRECT
variadic instance (params a$0/a$1 correctly replicated!) but that
instance is BODILESS — cf-catch fired for it; the throw is resolve()
of `make` (the mem-init's callee) during the deferred conversion,
BEFORE deduction (gfta never entered for 'make'; res-unknown/nomatch
probes silent — the throw is one of resolve's other exits).
Discriminant stands: N=2 pack fails, N=1 passes — the mem-init
call-argument pack expansion `forward_<Args>(a)...` for N>=2 in a
DEFERRED member conversion (compound_type replication notes say
single-element substitution is handled in method_bodies; N>=2 path
suspect).  Resume: dump the scoped ctor's mem-init irep before/after
replication (compound_type ~590-720 expanded_record), then check
method_bodies' `a$k` lockstep for the ARG-level pack.

## Round 24b (2026-08-08 evening): N>=2 pack front-stamping fixed — 2 flips

Root of the scoped_node/umap family: SIX unguarded "[temp.variadic]/7
substitute pack names with actual types" blocks
(cpp_instantiate_template.cpp x4 incl. the mem-init one at ~3924;
cpp_typecheck_method_bodies.cpp x2 at ~743/784) stamped the FRONT
element for ANY non-empty pack.  For N>=2 packs inside
not-yet-expanded patterns (mem-init `forward_<Args>(a)...`), element 0
was baked in before the per-element expander ran -> per-element call
unresolvable -> ctor body dropped via implicit-deletion recovery ->
uninitialized node -> umap duplicate-insert wrong-code.  Fix: guard
all six to pa.second.size()==1 ([temp.variadic]/5 comments).  Flips:
cpp17_scoped_node_pack_ctor + cpp17_umap_emplace_mixed_categories ->
CORE.  5 suites green; runtime g+++clang++ verified.  Diagnosis
technique that cracked it: STAGE DUMPS (scan for the pack name /
element tags at entry / after-expand / after-subst of
prepare_deferred_method_body) — pinned corruption to BEFORE the drain,
then instantiate-entry probe pinned it to instantiate_template itself.
Lesson: probe INVENTORY of front()/[0] pack accesses
(`grep 'pa.second.front()'`) finds this whole defect class; the two
/7 blocks in method_bodies remain front()-based for N==1 only.
Background: cz1 (vector pointer-diff) + cz3 (map operator[] rref
no-body) cvise running; sig probes for abstract_env/restrict_fp TUs.
NOTE: cz3's no-body operator[](rref) may share this same root — check
against the fixed binary when it converges (the reduction runs the
OLD binary! criterion may go stale — verify harvest against NEW).

## Round 24b probes (parked tests, on the FIXED binary)

- restrict_function_pointers_tu: NO LONGER SCALE-BLOCKED — completes
  in <90min: 184 of 87623 FAILURE, all pointer-deref class, dominant
  cluster "deallocated dynamic object" on _M_next/ref_count/hash_code
  (libstdc++ internals; use-after-free-shaped).  Now a diagnosis
  target: pick ONE deref property, --trace it, find whether a dtor /
  deallocate runs early (cf. constexpr-dtor arc) or a body is
  wrong.  Output kept at /tmp/sig_cpp17_restrict_function_pointers_tu/.
- abstract_environment_tu: converts + reaches BMC, solver times out
  at 3600s — genuinely scale class (with ofstream/erase_if).
- cz1 (vector size.pointer.1) + cz3 (map operator[] rref no-body)
  criteria RE-VERIFIED against the fixed binary — both still fail,
  reductions remain valid (cz1 74%, cz3 57% at check time).

## Round 25 (2026-08-08 late): set_insert CORE'd — 2 fixes, 13th flip

Fix 1 (fifth TT-instance consumer): disambiguate_template_classes'
instance fallback used ROOT-scope RECURSIVE template lookup which does
not descend into namespaces; std::__1::allocator unfindable.  Fixed:
when empty, look up in the GRANDPARENT of the instance's id_map entry
(instance sits inside the template's param scope; its parent's parent
is the namespace) — [namespace.qual].
Fix 2 ([temp.local]/1): #tmpl_param_shadow marking extended from
top-level bare refs to refs nested in pointer/array/merged_type
declarators AND template-id arguments (+ ambiguous wrapper).  Root
chain: pointer_traits<_Tp*>::rebind=_Up* and rebind_alloc=
__allocator_traits_rebind_t<allocator_type,_Other> captured enclosing
int; unique_ptr deleter = __tree_node_destructor<allocator<int>>;
get() returned int*; __emplace_unique_key_args threw at static_cast,
swallowed by syshdr guard, body dropped, inserts lost.
KEY DEBUG TECHNIQUE (reusable): sfinae_contextt passthrough under
CBMC_DBG2 (keep real handler) + setenv("CBMC_DBG2") scoped in
convert_function to ONE symbol's drain — surfaces THE swallowed error
with full instantiation context.  Faster than gdb catch throw.
Impact: 4 libcxx tests crossed 2^8 objects (MORE code converts) —
--object-bits 12 added; both deque tests now fully VERIFY.
map tests' residual: __tree::destroy null/deallocated derefs on
__nd->__left_ (recursion on nondet left pointers — next layer).

## Round 25 cont.: fleet postmortem

- cz3 (map operator[] rref no-body): criterion DIED mid-flight — the
  round-25 capture fix removed the no-body; cpp20_map_basic now
  converts fully into BMC (no unwind flag -> BMC doesn't terminate;
  cpp20 family needs desc flags work).  Archived harvest.
- cz1 (vector size.pointer.1): converged 2.7MB -> 163B DEGENERATE:
  bare struct with UNINIT __begin_/__end_ + subtraction.  Valgrind
  gate is blind to uninit pointer SUBTRACTION (flags only jumps/deref)
  and the same-object failure on uninit members is CORRECT cbmc
  behavior.  LESSON: pointer-diff criteria need an INITIALIZATION
  witness (e.g. require native binary to assert vector invariants AND
  cbmc's model to violate them) — else any uninit pair matches.
  DIAGNOSIS REDIRECT: the real cpp20_vector failures are the
  uninit/havoc member class — find WHICH ctor/assign body is dropped
  in the real test instead of reducing.
- Live binary under long cvise fleets is a footgun: rebuilds change
  criteria semantics mid-run (cz3's death was silent).  Copy the
  binary per-fleet next time (cp build/bin/cbmc /tmp/czN/cbmc.pinned).

## Round 25 cont. 2: vector-family root surfaced (not yet fixed)

cpp20_vector_basic diagnosis (fixed binary, --object-bits 12 now
needed): ctor inits fine (begin/end/cap NULL); push_back allocates,
constructs 42; __swap_out_circular_buffer's std::swap chain writes
v.__end_ and v.__end_cap_ CORRECTLY (&dynamic+4) but
v.__begin_ = INVALID-514 — sourced from
__uninitialized_allocator_move_if_noexcept<alloc,reverse_iterator×3>
whose RETURN VALUE is malformed: trace shows
{ .__t_=NULL, .current=INVALID-514 } — a reverse_iterator with an
EXTRA __t_ field (std::__exception_guard's member fused into the
return struct?!) — wrong return type/layout for the
trivially-movable overload (uninitialized_algorithms.h 638;
`return std::move(__first1,__last1,__first2)` over reverse_iterators;
historical swallowed error 'symbol _Bp is unknown' in this
instantiation — __conditional_t's bool own-param, conditional.h 54).
NEXT: (1) check __is_cpp17_move_insertable/enable_if selection —
which overload got instantiated; (2) DBG2-passthrough on its drain
for the surviving swallowed error; (3) suspect non-type (bool)
own-params in alias bodies — mark() collects only TYPE param names?
check own_param_names collection for `bool _Bp`.
Affects: vector_basic, libcxx20_vector, map_basic (+ ranges family
via vector). All need --object-bits 12 + likely --unwind for BMC
termination once fixed (map_basic BMC no longer terminates without
unwind — desc flags work needed at flip time).

## Round 26 (2026-08-09): vector onion — two layers peeled, one left

Layer 1 FIXED: alias-instance redecl first-wins ([temp.spec.general]/5;
_And<...> FALSE→TRUE flip under drain guard killed the drain).
Layer 2 FIXED: deduction-path alias expansion skipped NON-TYPE args
([temp.alias]/2; `_Bp` dangled, both allocator_traits::construct
overloads discarded).  5 suites green ×1 cycle, committed.
Layer 3 OPEN: drain STILL throws with NO diagnostic — bare throw in
resolve() from typecheck_side_effect_function_call (gdb catch-throw
inventory: 26449 throws total; last-before-cf-catch bt =
resolve→typecheck_expr_cpp_name→typecheck_side_effect_function_call,
i.e. an unresolvable CALL in the 604 body under the syshdr guard with
messages suppressed even under DBG2-passthrough = the throw site
prints nothing (likely the `if(!fail_with_exception) throw 0` style
silent SFINAE exit).  NEXT: find which call in
uninitialized_algorithms.h 604-620 fails — candidates:
allocator_traits construct (now viable?), __make_exception_guard,
_AllocatorDestroyRangeReverse ctor, std::move_if_noexcept over
reverse_iterator, ++/!= operators.  Approach: probe resolve()'s
silent-throw exits to print base_name under DBG2 (there are >1 exits
without error(); grep `throw 0` near "silent" comments in resolve),
or bisect by instantiating each callee shape in a repro.
Probes used this round are all documented in this file's r25 entry
(sfinae passthrough + drain-scoped setenv + SIGTRAP-at-probe).

## Round 26 cont.: layer 3 narrowed to __to_address chain

resolve-throw unwind probe (RAII dtor + std::uncaught_exceptions,
printing base_name under drain-scoped DBG2 — ANOTHER reusable probe)
shows the fatal cascade: type -> __enable_if_t -> __to_address ->
to_address; the LAST __to_address failure propagates to the drain
catch.  `std::__to_address(reverse_iterator)` must select the
operator-> helper (pointer_traits<reverse_iterator> has no
to_address).  Header-free repros of (a) the full
to_address/helper/decltype chain (ta1.cpp) and (b) the C++20
requires-disjunction operator-> (rq1.cpp) BOTH PASS — missing
ingredient is subtler: candidates = std::prev(current).operator->()
in the else-branch, the `pointer` typedef via
__rebind_pointer_t/iterator_traits, or interplay of the constrained
operator-> lookup under the helper's decltype.  vector_basic now
fails 11 of 5537 (down from 15/5614-era shape; layers 1-2 committed
3b6ba50735).  NEXT: extend ta1 with (1) constrained operator-> as in
rq1 COMBINED, (2) a real prev()/pointer-typedef chain; or drain-probe
which sub-name of the __to_address resolution throws (the resolve-
throw probe stack prints innermost-last, so add depth indices).

## Round 26 cont. 3: concepts kernel fixed — compound-requirement eval

ta3 (10-line real-header __to_address(reverse_iterator), banked as
KNOWNBUG cpp20_to_address_reverse_iterator) revealed the LAYER-3
kernel: compound-requirement `{E} -> C<T>` evaluation left NESTED
type-predicate operands (type_arg1/2 named subs under `&&`) unbound —
apply(exprt)'s unnamed-child recursion goes through the typet
overload which doesn't know predicate nodes.  Header-free wrong-code
repro cr1.cpp -> CORE cpp20_compound_requirement_concept.  Fix is
LOCAL to compound_requirement_is_satisfied (children-first walk);
GLOBAL apply(exprt) fixes segfaulted cpp20_concept_iterator_chain
(quadratic re-walk + detach of shared <ranges> concept bodies; two
variants tried: unconditional expr-routing, depth-guarded outermost
walk — BOTH exploded; the pre-existing subst_params lambda recursion
is the amplifier).  LESSON: template_map.apply(exprt) is a hot path
over SHARED trees — fix consumers, not the walker.
ta3 STILL drops main after this fix (more __to_address onion:
next candidates per resolve-throw = element_type/__void_t chain,
_HasToAddress, or __decay_t of the helper return).  vector family
still blocked behind it.  same_as/_CmpUnspecifiedParam ordering.h
noise (recoverable) remains a separate large field.

## Round 27 (2026-08-09 evening): __to_address onion — 2 kernels found

Path: ta6 (_And<is_class<RI>,_IsFancyPointer<RI>> direct = FAILURE)
— every hand-repro passed, so cvise'd preprocessed ta6 (23-line
harvest in 40 min; markers kept for syshdr attribution; PINNED binary
per r25 lesson; criterion = specific assertion FAILURE + native
runtime gate).  Harvest analysis yielded:
1. KNOWNBUG cpp20_spec_match_two_phase (20 lines, dual-verified):
   partial-spec pattern `decltype(to_address(_Pointer()))` naming a
   LATER-declared function is wrongly selected — CBMC lacks two-phase
   lookup ([temp.res.general]/1, [temp.dep.candidate]/1); natively the
   sub fails softly and the PRIMARY is chosen.
2. The real-chain variant: the same late-decl spec-match failure
   ESCAPES during _IsFancyPointer<RI>'s static-member-initializer
   elaboration (value member never materializes) → `_Pred::value`
   unresolvable in __and_helper → _And falsely false_type →
   __to_address loses both overloads.  Note _HasToAddress in REAL
   libc++ pointer_traits.h line ~189 names to_address DECLARED BELOW
   IT (line 231) — the SAME two-phase shape, so fixing #1 correctly
   (primary selected softly) likely fixes the whole chain.
Diagnosis details: instance tag scope entered via resolve_scope
fast-path id_map find WITHOUT elaboration (suppress_elaborate=1);
tried elaboration there — instance complete, comps=0, value member
genuinely absent (static members aren't components; the MEMBER SYMBOL
was never created because the initializer threw).  Reverted that
speculative fix; the spec-match two-phase fix is the true root.
FIX SKETCH: at the spec-match candidate loop (instantiate_template
~1560-1730) and/or resolve-time function lookup, restrict unqualified
dependent-name candidates to declarations preceding the TEMPLATE
DEFINITION POINT (store a decl sequence number on symbols?) — large;
NARROW alternative: treat resolution failure of a pattern decltype
as soft candidate rejection AND make member-initializer elaboration
contain spec-matching throws (select primary, [temp.deduct]/8).
Background: rfp trace (prop 2775) running; libcxx20_vector probe
running; da1 archived.

## Round 27 cont.: rfp + vector probe results

- restrict_fp trace (prop 2775): _Fwd_list_node_base ctor runs with
  this == &is_deallocated!0 (CBMC-internal symbol!) — a mis-returned
  pointer (__t/return_value chain) aliases internal bookkeeping;
  same returned-garbage class as vector's INVALID-514.  Suspect a
  bodiless/mis-converted allocator or node-create path in libstdc++
  forward_list (irept/forward_list_as_mapt TU context).  NEXT: find
  which return_value first goes wild (grep trace backwards from state
  4313), check no-body/HIDE markers.
- libcxx20_vector (with --object-bits 12): completes, 22 of 5537
  FAILURE incl. main.assertion.1 line 9 'size' — same vector family,
  waiting on the two-phase-lookup fix.

## Round 28 (2026-08-09 night): TWO fixes — two-phase + static-member kernels

Fix 1 (commit "two-phase lookup for partial-specialization patterns"):
two_phase_pattern_depth counter gates a declaration-order filter in
resolve(): while a partial-spec pattern is typechecked, ordinary-
lookup candidates declared LATER in the same file are dropped
([temp.res.general]/1, [temp.dep.candidate]/1); ADL still augments.
LESSON: the sfinae_context_depth-wide gate broke 43 tests (deferred
member bodies see later decls legitimately); scope gates to the
PATTERN only.  cpp20_spec_match_two_phase -> CORE.
Fix 2 (commit "resolve static members via symbol table + short-
circuit folding"): (a) qualified member lookup falls back to the
symbol table when the scope-tree entry is missing (member symbols =
instance name with OUTERMOST depth-0 tag- stripped); DON'T insert
scope entries inside resolve (live iterator corruption -> segv);
(b) partially-evaluated or/and initializers fold by short-circuit
STRUCTURALLY (no typechecking — re-entering the typechecker
mid-elaboration segfaults; from_integer only for
c_bool/signedbv/unsignedbv, else invariant violation).
ta5/ta6 (_And/_IsFancyPointer kernels) GREEN.  ta3 = one more layer
(the __to_address alias itself still throws; resolve-throw showed
type scope=template::8 = enable_if body + __to_address + to_address).
5 suites green after both fixes.

## Round 28 cont.: ta3 next kernel + cascade measurement

ta3's fatal is now `invalid implicit conversion from 'void' to
'signed int *'` — __to_address RESOLVES (fix-2 cascade) but the
constrained overload's return type
`__decay_t<decltype(__to_address_helper<_P>::__call(declval<...>()))>`
evaluates to VOID (the decltype chain fails silently and degrades).
NEXT KERNEL: return-type decltype of a static member call through
__to_address_helper — repro shape: constrained fn template whose
return is __decay_t<decltype(Helper<T>::call(declval<const T&>()))>
with Helper's call itself decltype-returning.  Once fixed, expect ta3
+ possibly vector family (counts still 11/22 of 5537 — unchanged, so
the void-return IS the active blocker; map_basic still in BMC).
Reusable gotchas this round: from_integer invariant on non-bv types;
scope-entry insertion inside resolve() = live-iterator corruption;
folding must be structural (no typechecking) mid-elaboration.

## Round 29 (2026-08-10): decay ref-spec kernel FIXED; recursion arc remains

vr-series bisection (repro-first worked this time): the void-return
was TWO stacked defects.
FIXED (commit "strict P/A reference matching + context-aware alias
cycle keys" + CORE cpp11_alias_ref_spec_pointer_arg):
(a) disambiguate_template_classes' spec-match loop never opted into
strict_cv_deduction (4th site, round-17 family): `decay_<T&>` matched
`decay_<int*>` by stripping `&` -> decay_t_<int*> = int.  13-line
kernel.  (b) alias cycle keys now include the innermost instantiation
frame ([temp.point]) + absolute same-spelling depth cap 20.
REMAINS (vr5.cpp, 16-line real-header): std::__to_address(arrow_it)
still returns VOID — genuine same-frame recursion: computing the
fancy overload's return type nests overload resolution of
__to_address(int*), which AGAIN evaluates the fancy candidate's
return type BEFORE its default-arg constraint discards it (the
defaults loop at ~9492 runs inside guess_function_template_args
before fn-type typecheck at ~9905, so WHY the constraint doesn't
discard for int* in the NESTED context is the open question —
standalone eval of the same constraint works, vr6.cpp).  260
alias-cycle breaks feed empty_typet (void) into the return.  NEXT:
probe the nested candidate's default-arg eval (is_anonymous catch at
9603 returns nil correctly?) — instrument whether the int* fancy
candidate reaches fn-type typecheck at all; if yes, find which path
bypasses the 9492 defaults loop (maybe explicit-template-args path or
the apply_template_args route at 87/114).
5 suites green x2 (both commits).

## Round 30 (2026-08-10): recursion arc — probe inventory (no fix yet)

vr5 (__to_address on custom arrow class, real headers) probe results:
- id_set for `__to_address` is CORRECT (3 __to_address shapes only);
  the public to_address candidates seen earlier come from other call
  sites (shared_ptr machinery in <memory>).
- gfta-enter fired 594x ALL with arg0=tag-arrow_it — the nested
  deduction for `__to_address(int*)` NEVER happens: no default-ok/
  default-fail with a _Pointer->int* map ever appears (every map dump
  shows only 571/572/573/575::_Pointer->tag-arrow_it, one entry per
  nesting level).
- No `__p` unknown, no operator-> no-match — everything resolves.
- decltype results attributed pointer_traits.h:196
  (`decltype((void)declval<const _P&>().operator->())`, the _HasArrow
  spec pattern): 328x POINTER + 1x EMPTY.  Natively this decltype is
  ALWAYS void — the (void) cast is dropped 328 times (or the location
  attribution is misleading; standalone repro vc1.cpp of the same
  shape PASSES, so it is context-dependent).
NEXT (fresh turn): (1) determine whether the 196-attributed pointer
results are genuinely the _HasArrow pattern (print the full type +
enclosing candidate at that probe); if yes, find where the void-cast
is lost during PATTERN typechecking (spec-match context) — that would
flip _HasArrow<arrow_it> selection and explains everything: spec
mismatches (int* != void default) -> _HasArrow=false ->
_IsFancyPointer=false -> fancy __to_address discarded -> ... yet
defaults succeeded (enable_if<true>) — reconcile via the round-28
short-circuit fold (first operand constant TRUE from... check).
(2) The 594x same-arg re-deduction: find the RETRY loop driving it
(who re-resolves the same call; each retry re-attempts __decay_t →
260 alias-cycle breaks → void).
Probes to reuse: gfta-enter/default-ok+map/fntype-pre (this round's
patch set, in git stash-able form in this entry's history).

## Round 31 (2026-08-10): __to_address chain COMPLETE — 3 flips

THE fix ([basic.lookup.qual]/1): resolve()'s final-component lookup
used RECURSIVE unconditionally; qualified names now use QUALIFIED
(scope+bases+using, no parent escape).  A nonexistent member
(`pointer_traits<_P>::to_address`) fell back to the same-named
NAMESPACE function (std::to_address), wrongly validating the
detection-idiom spec pattern -> void-returning helper spec selected ->
__to_address returned void.  32-line kernel dz3.cpp (free fn +
qualified member ref in spec pattern), found via cvise on ha7 (ONLY
pointer_traits.h included — 1034 lines, <10 min converge, pinned
binary).  KEY INSIGHT for future arcs: when structural hand-repros
keep passing, cut the INCLUDE SURFACE down and cvise THAT — the
poison was an in-header interaction (free std::to_address visible),
not ecosystem caching.
FLIPS: cpp20_to_address_reverse_iterator, cpp20_vector_basic_libcxx,
cpp20_libcxx20_vector (all CORE, non-vacuous, native-verified).
Round-30's void-cast/(void) lead was a red herring (mis-attribution).
Vector-family residuals: map_basic OOMs in BMC (needs unwind flags
work — desc has none; solver scale now, not front-end);
ranges_basic still VACUOUS (main truncated; tied to ranges_pipe).
5 suites green.

## Round 31 cont.: map_basic re-measured

With --unwind 5 --no-unwinding-assertions --object-bits 12: NO MORE
OOM — completes with 25 of 5960 FAILUREs, cluster =
`*return_value_operator[]` derefs (map::operator[] returns a bad
reference; __tree insert-or-create path).  Now a diagnosable
wrong-code target (trace one operator[] property); desc will need the
unwind flags at flip time.

## Round 32 (2026-08-10): map operator[] arc opened

- std::set works on cpp20 (contrast test) — map-SPECIFIC.
- map::operator[](rref int) is CALLED but BODILESS with NO no-body
  property (the silent-havoc diagnostic gap again!); return_value
  havocs to header-interior pointers; 42 written into pointer bits;
  destroy() then walks garbage (the 25-failure cluster).
- Drain-scoped cf-catch caught the swallowed error: "found no match
  for symbol 'operator->'" — candidate IS the correct
  __tree_iterator::operator-> (return __rebind_pointer_t<...>,
  __tree:747) but gets REJECTED; immediately preceded by
  `tuple<? &&>` instantiations (nil type arg!) from map::operator[]'s
  piecewise path (__emplace_unique_key_args(k, piecewise_construct,
  forward_as_tuple(k), forward_as_tuple())).  Suspect: the empty
  forward_as_tuple() / tuple<> machinery produces a nil-typed arg,
  poisoning the drain; the operator-> rejection may be collateral
  (candidate return alias failing in-context — standalone
  __rebind_pointer_t works, mb3.cpp).
- SEPARATE second defect: mb4.cpp — on an EMPTY map,
  `m.find(1) == m.end()` evaluates FALSE (find/end comparison wrong
  or find havoc'd).  8-line repro, real headers.
NEXT: (1) trace the operator-> rejection: instrument
disambiguate_functions' rejection reason for that candidate, or
repro the piecewise emplace chain (tuple<?&&> lead) header-free;
(2) mb4 find/end as an independent smaller kernel — likely quicker;
consider starting with it.

## Round 32 cont.: find() root = __lower_bound ambiguity

Bisection: end()==end() PASSES; find(1)==end() FAILS on empty map —
find() is the wrong side.  __tree::find<signed_int> is CALLED but
BODILESS (again NO no-body property — silent havoc).  Drain probe:
"symbol '__lower_bound' does not uniquely resolve" — the const /
non-const member overload pair (iterator vs const_iterator returns,
alias-typed params __node_pointer/__iter_pointer printed in the
candidates UNRESOLVED: __conditional_t<1,...>, __rebind_pointer_t
<...>) ties instead of the non-const winning on the implicit object
parameter ([over.match.funcs]/4, [over.ics.rank]/3.2.6).
Hand-repros lb1-lb3 (incl. alias-typed params + member template
caller) ALL PASS — context-dependent again.  cvise ea1 RUNNING
(criterion = 'does not uniquely resolve' + cf-catch find<signed_int>
adjacency, typecheck-phase only via --show-symbol-table, PINNED
probe binary; 82k lines, ~50s/iter shrinking).
Also: mb2 caught operator-> no-match + tuple<?&&> lead for
operator[] (separate layer, after find is fixed).

## Round 32 final: find/__lower_bound FIXED (implied-object ranking)

Kernel (21 lines, CORE cpp11_member_template_const_overload): const/
non-const member-TEMPLATE pair with DIFFERING return types ties on
implicit member calls — member_template_const_penalty required
fargs.has_object; implicit calls have none.  Fix: derive the implied
object's constness from the enclosing member's this_expr
([over.call.func]/3).  Identical returns masked the gap via
remove_duplicates.  ea1 cvise: 82k → 42 lines in ~2h with the
TYPECHECK-PHASE criterion (probe binary + --show-symbol-table stops
before BMC — the runtime-free criterion trick, REUSE THIS).
mb6 (find==end) + mb4 GREEN.  map_basic still fails 25/5960 — the
operator[] layer (tuple<?&&> + operator-> rejection leads banked in
the round-32 opening entry).  5 suites green.

## Round 33 (2026-08-10): map operator[] FIXED — map_basic FLIPPED

Root (match-fail probe in fargs.match printed operand shape):
operator->'s implied object was `member` of `side_effect
function_call` — reference_binding's this-gate only whitelisted
DIRECT temporaries; member-of-temporary (xvalue, [expr.ref]/8,
[over.match.funcs]/5.3) returned false → operator-> no-match →
operator[] body dropped → silent havoc.  Fix: walk the member chain;
ultimate temporary compound ⇒ binding permitted
(cpp_typecheck_conversions.cpp reference_binding ~2619).
Kernel mx1 (24 lines): `make(7).first.get()` — pre-fix CONVERSION
ERROR (hard, not silent — only in-drain it silently drops bodies).
CORE cpp11_member_of_temporary_call + FLIP cpp20_map_basic_libcxx
(0/6002, 1 assertion, native clang++ green).  5 suites green.
The mb2 tuple<?&&> lead was NOISE (recovered deduction attempts);
the destroy-cluster derefs were downstream of the havoc'd insert.
8 KNOWNBUGs remain: ranges_basic (vacuous), ranges_pipe, restrict_fp,
regex, ofstream, abstract_env, erase_if, goto_symex_state_header.

## Round 34 (2026-08-11): perfect-forward pack onion — 3 layers fixed

ranges_basic truncation error surfaced DIRECTLY in output ("conversion
from int[N] to <<type:auto>>"); bisect: views::all/begin/ref_view all
OK, take_view CTAD fails.  ranges_pipe re-reduced via __invoke variant
(rp3).  Chain of harvests (fb1 82k→ stalled slow; fc1/fc2 fast via
248-line seed → 43 lines; fd1/fe1/ff1 re-grew layers post-fix):
kernels ek1 (empty trailing pack partial spec — CRASHED symex
assign_from_struct), ek2 (nonempty trailing pack — scalar-collapsed
Idx), ek4 (empty member pack decltype under outer deduction — main
dropped SILENTLY, no diagnostic, hti=0!).
FIXES (commit 3530826752): (1) build() kind-aware positional pack
split for multi-pack replays + sentinel; (2) resolve.cpp packaging
pack_expr_map splice (mirrors instantiate's); (3) apply() value-pack
sizing: empty pack present ⇒ ambiguous ⇒ leave for strip; (4) member-
fn-template path: strip empty-pack params + refs in declarator type
AND DECLARATION type (trailing-return decltype lives there!), sentinel
gate for ctor expansion, gfta candidate-signature strip, spec-packs
replay in drain class map.  3 CORE tests (9121cd8cbb).  5 suites green.
KEY DEBUG LESSONS: build-debug (RelWithDebInfo) + gdb breakpoint at
error-emission line = decisive when probe ping-pong stalls; thread_local
marker distinguishes same-line call sites; grep '^KNOWNBUG' matches
PROSE — count via head -1 only (8 true KNOWNBUGs, not 13).
NEXT LAYER (ranges_pipe still drops main): "symbol '__bound_args' is
unknown" — mem-init `__bound_args_(__bound_args...)` with NON-empty
packs at drain of __perfect_forward_impl ctor (tuple member restored
in fd1 harvest = f4.cpp still failed WITHOUT it... recheck).  Artifacts:
/tmp/f4.cpp /tmp/ff1/red.cpp /tmp/rp3.cpp; probes ALL STRIPPED.

## Round 34 cont.: layer 4 (own-pack varargs) fixed; layer 5 queued

fg1 re-reduction found layer 4: `operator()(_Fn, _BoundArgs...)` — my
round-34 empty-pack param removal deleted the VARARGS param
([dcl.fct]/6: `B...` with B non-pack = B + C varargs, NOT a pack
declarator!) whenever an unrelated trailing template pack deduced
empty.  Fix: own-pack name constraint in BOTH the in-declaration scan
and the original-declarator recovery (commit above).  Kernels mp4
(14-line, plain --cpp11, g++-valid!) + ek5 → CORE
cpp11_varargs_after_empty_pack + cpp20_mid_pack_decltype_invoke.
5 suites green.  Diagnosis chain that worked: empty-pack-slot probe →
post-gfta count (candidate EXISTS, non-template) → match-arity probe
(nparams=1/2 vs nops=2/3 — param VANISHED) → the removal site.
PROBE-REPAIR LESSON: python line-insertion before `return` under an
un-braced `if` SILENTLY REWRITES SEMANTICS — always insert braced,
verify with sed context print before building.
Layer 5 (fh1, 108 lines, STILL drops main): variant with
`__invoke(_Fp, ...)` varargs + trailing class... pack + decltype(_Op())
+ index_sequence_for<> (EMPTY).  /tmp/fh1/red.cpp saved.  Next: delta
fh1 vs fg1 (E-edit method) then kernel.

## Round 35 (2026-08-11): layers 5-8 of the perfect-forward onion

L5 (k4, 17 lines, plain cpp11!): bare `...` C-varargs param deleted by
TWO empty-pack removals (instantiate refs_pack + gfta
variadic_pack_empty) when an unrelated trailing template pack deduced
empty — own-pack rule applied at both ([dcl.fct]/6).
L6 (ek8, wrong-code 4097≠1): apply(exprt) subst_params scalar-
substituted the PACK name `_Idx` (in `get<_Idx>()...`'s template-args)
with the convenience/unassigned entry — packs only substitute by
EXPANSION ([temp.variadic]/5); skip pack names + unassigned there.
Also: value-pack drop kept when pattern names an UNKNOWN template-arg
(enclosing-class pack, [temp.variadic]/5 governing-pack rule);
prepare_deferred_method_body now replays #spec_template_packs.
L7 (ek9, symex crash): `get<_Idx>...` — bare fn-template-id VALUE
pattern parses with an ID-LESS template-args child (ambiguous-`<`
contexts, parser sites 7971/9507/11170 push raw irept).
has_template_args misses it → expanded elements resolved as the raw
template → nil args.  PARSE-SIDE NORMALIZATION IS FORBIDDEN: setting
the id in rTemplateArgs broke 3 tests (cpp11_variadic_ctor_pack_multi,
cpp11_variadic_get_partial_spec_deduce,
cpp14_variable_template_pack_partial_spec) — the id-less shape is
LOAD-BEARING ("maybe comparison").  Fix: normalize ONLY the expansion
output copy (template_map.cpp val_elems branch).
Commits: 3-fix bundle + normalize + CORE tests
cpp11_varargs_trailing_pack_invoke, cpp11_template_id_pack_expansion,
cpp11_fn_template_id_pack_value.  5 suites green ×2.
rp3 STILL drops main — layer 8+ reducing (fk1).  probes stripped.

## Round 35 close: layer 8 parked (possible degenerate)

fk1 (113 lines, archived): new ingredients = `invoke_result_t<void>
invoke(void());` + `__bind_back_op::operator()(_Fn __f, _BoundArgs)
-> decltype(invoke(__f))` where invoke's param void(*)() CANNOT take
__f=int(*)() (verified: both compilers reject the direct call) — yet
clang FULLY COMPILES the harvest TU (link-only failure on decl-only
__invoke).  So clang recovers via a SFINAE path CBMC doesn't; the
shape may be a reduction artifact rather than the true ranges
blocker (cz1 lesson — criterion drift toward compiler-laziness
attractors).  Hand kernels ek10/ek11 (compatible + overload-recovery
variants) both PASS.  PARK; next round: re-reduce ranges_pipe with a
STRONGER criterion — require native FULL COMPILE+LINK+RUN of a
variant with bodies (not just -fsyntax-only), plus the assertion
line, to keep harvests executable.
Round-35 totals: 4 commits (3-fix bundle, normalize, 2 test commits),
4 CORE tests, layers 5-7 fixed, 5 suites green, probes stripped,
tree clean.  ranges_pipe/ranges_basic remain KNOWNBUG (8 total).

## Round 36 (2026-08-11): 4 flips + regex abort fixed (sound demotion)

FLIPS: ofstream_from_string -> CORE (0/15085, ~23s);
restrict_function_pointers_tu, goto_symex_state_header (harness assert
ADDED), abstract_environment_tu -> THOROUGH (each verifies its
harness assertion with --property main.assertion.1; 6-11 min > CORE
budget; other FAILUREs = sound havoc of out-of-TU fns, e.g.
get_nil_irep bodiless in TU -> +60-displaced return values are
HAVOC, not front-end bugs).  --property = the principled treatment
for dog-food converts-tests.

REGEX ARC: crash was ASLR-dependent (3/3 vs 0/3 via setarch -R —
THE diagnosis lever for layout-dependent bugs).  Root chain:
(1) scope id-sets std::set<cpp_idt*> iterate in ADDRESS order;
(2) on some orders, syshdr bodies HALF-typecheck: under
convert_function's syshdr_guard (null handler), several paths REPORT
errors WITHOUT THROWING and continue (allocator/basic_string
no-matches in locale/string bodies; DBG2 passthrough shows them all),
leaving e.g. `return nullptr;` unconverted ([conv.ptr]/1 skipped);
(3) goto-convert emits lhs void* := rhs nullptr_t* -> symex abort.
COMMITTED: final sweep demoting syshdr bodies with inconsistent
returns to no-body (sound havoc).  regex: abort GONE, verifies on
most layouts (~91-300s), some layouts slow (more demotions) -> stays
KNOWNBUG with notes.
ORDINAL LESSON: a creation-ordinal comparator on the scope sets made
half-conversion DETERMINISTIC (great for diagnosis) but BROKE
cpp17_std_function_lambda_call (its _M_get_pointer stops converting
under creation order!) — resolution order-sensitivity cuts both ways;
canonical ordering needs the first-wins consumers fixed first.  KEEP
THE PATCH IDEA for diagnosis sessions (apply locally, don't commit).
NEXT (regex precision arc): make error-report-without-throw paths
under syshdr_guard either THROW or recover consistently; candidates
visible in the DBG2 dump: mem-init allocator ctor no-match recovery,
implicit_typecast failures, do_grouping-family string-literal
returns.  ALSO pending: erase_if VERIFICATION ERROR diagnosis; fl1
ranges reduction (~2min/iter, slow).

## Round 37 (2026-08-12): erase_if flipped (SMT backend)

ERROR verdict = "SAT checker ran out of memory" (>50G, even ONE
property, unwind 3, slice-formula, any object-bits).  Equation is
SMALL (34k steps, 4132 live, 1 VCC, no giant arrays/constants/divs —
the 323k "/" grep hit was COMMENT slashes, beware).  --smt2 converts
(13MB) and z3 solves UNSAT in ~4min → CBMC --smt2 end-to-end
VERIFICATION SUCCESSFUL 6m15.  Flipped THOROUGH smt-backend (README
tag: tests requiring SMT).  --incremental-smt2-solver z3 FAILS:
convert_expr_to_smt lacks extractbits (solver-side gap, noted).
DIAGNOSIS PATTERN for solver OOM: program-only dump → live-step count
→ op census → SMT2 cross-check → z3.  3 KNOWNBUGs remain: regex
(syshdr-swallow precision arc), ranges_pipe (fl1 still ~236 lines,
criterion too slow ~2min/iter — consider re-seeding from the
90s-typecheck criterion instead), ranges_basic.

## Round 37 close: ranges_pipe reduction exhausted

fm1 (fast 0.18s/iter criterion: native compile+run gates +
typecheck-phase could-not-typecheck check) reconverged to 236 lines =
the existing test file is textually MINIMAL.  fl1's slow criterion
(full BMC 90s/iter) wasted 14h for 12 lines — ALWAYS use the
typecheck-phase criterion for drop-main bugs.  Remaining ranges work
= E-delta layer analysis (rounds 34-35 method), NOT reduction.
CONVERGENT NEXT ARC: the syshdr-guard "report error without throw"
swallow fix would serve BOTH regex precision AND the ranges drop-main
family (same "could not fully type-check" leniency).  Candidate
swallow sites visible in round-36's DBG2 dump: allocator-ctor
no-match in mem-init recovery, basic_string ctor no-match,
implicit_typecast failures that print + continue.  Fix pattern: in
sfinae/null-handler contexts make each site either THROW to the
body-level recovery or recover to a TYPE-CONSISTENT node — never
print-and-continue with a half-node.
KNOWNBUG count: 3 (regex, ranges_pipe, ranges_basic).  Campaign
start: 21.

## Round 37b (2026-08-12): KNOWNBUG coverage audit

User asked: is every known problem covered by a test?  Audit result:
1. regex / ranges_pipe / ranges_basic: KNOWNBUGs exist ✓.
2. syshdr print-without-throw swallow: was UNCOVERED → NEW KNOWNBUG
   cpp11_syshdr_swallow_demotions (std::to_string minimal trigger;
   DISALLOWED-pattern 'inconsistent return' — verified it FAILS as
   CORE today; flips when the swallow sites are fixed).  Disallowed
   patterns = the tool for "works but loses precision" bugs.
3. Scope-set order-sensitivity (std_function_lambda_call breaks under
   declaration-order iteration): NOT runnable as a KNOWNBUG (can't
   encode allocator layout in test.pl); documented as a warning in
   that test's desc + here.
4. incremental-smt2 extractbits gap: reproducer = erase_if TU +
   --incremental-smt2-solver (bv[8] extract from typecast(bv[32],
   index(...)) — a CPP-frontend bv shape); minimal C/C++ trigger NOT
   yet found (bitfields, unions, virtual dispatch, char-cast-of-index
   all pass).  Documented in erase_if desc; upstream test deferred
   until a small trigger exists.
5. Speculative, unconfirmed (no test): lambda-body return_type
   save/restore in typecheck_expr (cpp_typecheck_expr.cpp ~6414) is
   not exception-safe (plain assignment, no scope guard) — same
   hazard convert_function fixed; would only bite if body typecheck
   throws mid-lambda and is recovered upstream.  Verify before
   testing.

## Round 38 (2026-08-12): lambda return_type hazard — investigated, hardened, grounded

VERDICT: real code hazard, NO reachable trigger.  Evidence:
(1) code review: plain-assignment restore, skipped on throw; window =
same-enclosing-body continuation after an expression-level recovery.
(2) corpus probe (rethrow-detector around the body typecheck): ZERO
hits across the full cbmc-cpp suite + regex TU.
(3) direct search: every VALID lambda body tried (goto, local
classes, try/catch, static locals, range-for, nested lambdas, unions,
statement-exprs) typechecks — no CBMC-throwing valid body found to
weaponize a SFINAE-context clobber.
ACTION: scope-guard hardening (mirrors convert_function) + TWO CORE
tests: cpp11_lambda_return_context (enclosing double-return conversion
intact across int-lambdas — would catch any future clobber) and
cpp11_lambda_break_rejected ([stmt.break]/1 rejects-invalid — the
loop-context flags turned out CORRECT already; pinned).  Guard scope
audited: closes at the same block as the old mid-scope restore; no
return_type reads in between.  5 suites green.
Every known issue now has committed grounding: 4 KNOWNBUGs (regex,
ranges_pipe, ranges_basic, syshdr_swallow_demotions), THOROUGH x5,
CORE tests for all fixed/hardened behavior.

## Round 39 (2026-08-12): swallow arc — 2 roots fixed, tracker FLIPPED

ROOT 1 ([temp.inst]/11): still-deferred never-odr-used members carried
RAW parse trees into goto conversion — now cleared pre-conversion
(cpp_typecheck.cpp).  Killed ALL to_string demotions.
ROOT 2: type2name threw std::string on constructor/destructor return
types (C++ struct components include methods!); cpp recoveries catch
only int → the exception ESCAPED convert_function mid-body (window
probes: pass-1 pre-try→no-tc-ok/no-catch), a SECOND conversion then
mangled the half-body silently.  Fixed: stable CTOR/DTOR spellings.
regex now converts on EVERY layout (8/8).  DIAGNOSIS GOLD: the
window-open/close + tc-ok/tc-catch marker pattern; catch-by-TYPE
probes (string/cstr) identified the foreign exception in one run.
FLIPPED: cpp11_syshdr_swallow_demotions → CORE.  regex: conversion
done; solver-time layout variance remains (KNOWNBUG, notes updated).
RANGES ARC RESUMED: mem-init own-pack expansion fixed (expand_own now
dispatches on member_initializer nodes too) — '__bound_args unknown'
gone; NEXT LAYER surfaced cleanly: __tuple_impl 3-pack ctor no-match
(args [indices,types,indices,types] vs the _Uf/_Tf/_Up ctor —
deduction of the multi-pack member ctor).  2 KNOWNBUGs left:
ranges_pipe, ranges_basic (+ regex solver-only).

## Round 40 (2026-08-12): inherited-ctor-template temporaries + mem-init packs

FIXED ([class.inhctor.init]/1 + [conv.ptr]/3): a base ctor TEMPLATE
inherited via scope alias materialized the temporary as the BASE type;
`bb(f,0)` returned pf → conversion error → CALLER dropped silently
(wrong-code, ic3 29-line kernel, CORE
cpp11_inherited_ctor_template_temp).  Fix: snapshot the written
cpp_name; retype temp to D + typecast this to B*; gate = ctor NOT a
D-component (imported non-template ctors already work);
cpp_constructor rebinding taught the typecast-wrapped form (its
DATA_INVARIANT aborted the 4 inheriting-ctor tests before the gate +
shape fix — first attempt DOUBLE-patched, watch for that).
Also expand_own hardening: unmatched pack expansions kept unless
governed by a KNOWN-EMPTY pack; pack-size-driven replication fallback.
5 suites green.
RANGES STATE: '__bound_args unknown' FIXED; the __tuple_impl no-match
persists — diagnosis so far: candidate ctor template's gfta SUCCEEDS
(instance nparams=4, no this/Up) but fargs=4 (the `__u...` delegation
arg dropped UPSTREAM of resolution, NOT by expand_own's new branch —
verified by the ti-cand/ti-gfta/ti-nil probe set).  Next: find who
drops `__u...` from the delegation call before resolution (suspects:
instantiate-time ctor mem-init machinery 3760+/7150+ in
cpp_instantiate_template.cpp, or apply()'s ambiguous-args machinery).
fn1 reduction: file is minimal for THIS criterion too (whole chain
load-bearing).  2 KNOWNBUGs + regex-solver remain.

## Round 41 (2026-08-12): alias-qualified using B::B + placeholder hygiene

FIXED: (1) inheriting-ctor detection now resolves the using-qualifier
through ALIASES ([namespace.udecl]/1 + [class.qual]/2) — libc++'s
`using __perfect_forward<...>::__perfect_forward;` finally imports;
the [class.qual]/2 terminal==qualifier-last-name gate keeps ordinary
member using-decls (std::list `using _Base::_M_impl;`) unaffected
(list_basic regressed before the gate!).  (2) unassigned placeholders
now get their TYPE typechecked at return (raw `long` leak into
`_Ep - _Sp`); the THROW variant regressed is_constructible_real_pair
+ list_basic — placeholder-survival is a load-bearing contract
(cpp_typecheck_compound_type ~3402 comment says so; verified).
5 suites green.  RANGES NEXT LAYER: "symbol '_Idx' does not uniquely
resolve: constructor void() / constructor void(void)" — a scalar _Idx
use resolving to two synthesized ctor signatures (?!) during pf
elaboration.  Probes all stripped; base.cpp still drops main.
KNOWNBUGs: ranges pair + regex-solver.

## Round 41b (2026-08-12): coverage audit #2

Question: is every known problem covered?  Result:
- ranges pair + regex-solver: KNOWNBUGs ✓ (interior layers incl. the
  current "_Idx does not uniquely resolve" are covered by the failing
  ranges tests themselves).
- Round-41 alias-qualified inhctor fix: was UNPINNED → NEW CORE
  cpp11_inherited_ctor_alias_qualifier (revert-verified: FAILURE
  pre-fix, wrong-code).
- Round-41 placeholder-type hygiene (fix 2): NOT standalone-reachable
  (aq2 kernel passes even with fix reverted — needs the full ranges
  context); covered via ranges KNOWNBUGs until they flip, then their
  CORE forms pin it.  Noted here as residual-risk-accepted.
- Round-39 mem-init own-pack expansion (0aed0eb2d6): revert-test shows
  NO existing test catches it standalone either — same status: pinned
  transitively by the ranges KNOWNBUGs; will be pinned by their flips.
REVERT-TEST HYGIENE LESSON: restore with `git checkout HEAD -- file`,
NEVER the fix commit (an intermediate commit resurrected a stale file
minus round-40 hardening; caught via git status before any damage).

## Round 42 (2026-08-13): the _Idx layer — pack identification per [temp.variadic]/5

FIXED (3 sub-defects in typecheck_template_args' expansion collector):
(1) nested-expansion skip — packs inside an ellipsis-marked subtree
belong to the INNERMOST expansion ([temp.variadic]/5); (2) scope-precise
name→parameter mapping ([basic.scope.temp]) via RECURSIVE lookup,
APPLIED ONLY when the looked-up parameter intersects the pack maps
(unconditional exact matching regressed tuple/function/apply — patterns
re-typechecked cross-scope legitimately need the suffix fallback);
(3) live-over-stale same-spelling filter before the length-consistency
check.  Plus convert_template_parameter: unassigned placeholders now
take the pack fallbacks (pack maps take precedence over seeded
placeholders; non-pack placeholders keep survival), and the non-type
front-element convenience (pack_expr_map analogue of pack_args_map).
The double-ctor error text decoded: empty-pack sentinel (ID_type of
empty_typet) fed to make_constructors → POD ctors void()/void(void).
CORE cpp14_nested_pack_same_spelling pins all of it (assertion 3 also
guards the swallow).  5 suites green.
RANGES NEXT LAYER: "found no match for symbol '__tuple_impl'" — ctor
matching with __tuple_indices/__tuple_types argument pairs.

## Round 43 (2026-08-13): tuple ctor onion — 4 fixes, 3 CORE tests

FIXED (commit "libc++ tuple constructor onion"):
(1) replace_value_pack_ref — non-type pack in TYPE pattern gets i-th
VALUE ([temp.variadic]/5); tuple_types collapsed to <char,char> before.
(2) late aggregate base-init lowering in typecheck_member_initializer
([class.base.init]/7 + [dcl.init.aggr]/1) — ctor-TEMPLATE instantiations
never pass full_member_initialization; gate = no user ctor AND no vtptr
(virtual13 caught the missing /1.3-1.4 exclusion); shape = the eager
path's explicit-constructor-call assignment (cpp_constructor routing
broke base-less single-operand aggregates — no paren-init path there).
(3) #base_type-exact matching in full_member_initialization
([class.base.init]/1-2) — synthesized copy-ctor initializers cross-wired
same-named __tuple_leaf bases; name shortcut KEPT for explicit inits
(two_leaf lockstep test relies on positional consumption; ordinal
variant also failed — dropped arguments).
(4) #sizeof_pack guards in pack_subst stamping + replace_*_pack_ref +
subst_elem ([expr.sizeof]/5) — sizeof...(_Tp) degraded to element BYTE
size under converting-element construction.
CORE: cpp11_aggregate_base_pack_meminit (g++/clang), 
cpp14_libcxx_tuple_ctor_kernel, cpp20_tuple_class_element (clang).
5 suites green.  NEXT LAYER: tb6/tb7 — `get`'s by-value slicing
static_cast<__tuple_leaf<T>>(__t.__base_) fails ("unexpected
expression: struct" / "invalid implicit conversion from 'const struct
__tuple_leaf' to 'struct box'") when the element is CLASS-typed.
Kernels /tmp/tb6.cpp /tmp/tb7.cpp reproduce.

## Round 43b (2026-08-13): get-slice layer opened, [dcl.init.list]/3.2 fix

gs3 (18-line, no templates): by-value slicing static_cast broke under
the NEW aggregate lowering — the synthesized copy ctor's single sliced
same-type initializer was element-wise-initialized instead of
copy-initialized ([dcl.init.list]/3.2 + [dcl.init.general]/16.6.1).
LATENT: all 5 suites were green with the bug present — only the
kernel caught it.  Fixed (same/derived-type single-operand skip) +
CORE cpp17_sliced_base_copy.  LESSON: after adding an interception
path, always test the SYNTHESIZED-member shapes (copy/move ctor)
against it, suites under-cover them.
NEXT ARC (tb6/tb7 kernels, /tmp): converting-element tuple ctor
(tuple<box<int>> t(3)) — instance symbol EXISTS with EMPTY Value, zero
errors even with DBG2 passthrough: body never converted or queued (not
a swallow).  Suspect: ctor instantiated during list-ELEMENT conversion
inside the new aggregate lowering path misses the odr-use/drain
bookkeeping (odr_used_by_member_initializer analogue).  tb2/tb6/tb7
all reduce to this.  Ranges pipe still vacuous behind it.

## Round 43c (2026-08-13): coverage audit #3

Question: every known problem covered by a committed test?  Fixed two
gaps found:
- silent ctor-drop arc (tb7) was /tmp-only → NEW KNOWNBUG
  cpp20_tuple_converting_element (clang-verified kernel; no-body +
  assertion FAILURE currently).
- rejects-invalid gap noticed in round 43 (ti1 v1): kind-mismatched
  non-type pack deduction ACCEPTED ([temp.deduct.type]/17; g++/clang
  reject with "deduced non-type template argument does not have the
  same type") → NEW KNOWNBUG cpp11_deduced_nontype_kind_mismatch.
  (First ri1 draft was a most-vexing-parse false positive — verify the
  REJECTION REASON, not just the exit code.)
Still transitively-covered-by-design (documented round 41b): placeholder
type hygiene, mem-init own-pack expansion (pinned when ranges flips).
KNOWNBUG census now 5: ranges pipe + ranges basic + regex-solver +
ctor-drop + kind-mismatch.

## Round 44 (2026-08-14): ctor-drop arc — 2 layers peeled; /17 parked

PARKED: [temp.deduct.type]/17 kind-mismatch rejection — enforcement at
build_template_args broke VALID tuple kernels (CBMC parks deduced
values with normalized kinds; internal value-typing must be fixed
first).  Guidance in the KNOWNBUG desc.
FIXED (commit "empty-pack classification and sizeof... survival"):
(1) pack_size_map==0 is authoritative over stale same-parameter
element entries (sequential same-template instantiations share the
identifier; deduction never erases) + scope-exact classification skips
the suffix-ambiguity veto (the parameter's OWN leftover convenience
entry vetoed its zero-length expansion — cpp14_nested_pack_same_spelling
assertion 3 caught the first attempt's gap).  (2) two more
#sizeof_pack-unguarded stampers in prepare_deferred_method_body.
DIAGNOSIS TECHNIQUE: instrumented all 20 message-less `throw 0` sites
(braced insertion — the un-braced-if probe hazard bit again, caught at
build via -Werror=misleading-indentation); the escaping throw was the
[temp.deduct]/8 qualified-::type SFINAE throw firing from the DRAIN
(no deduction in flight).  Half-elaborated instances stay CACHED — an
instantiation whose member-alias elaboration throws recoverably leaves
a poisoned symbol (future arc if it recurs).
REMAINING (cpp20_tuple_converting_element still KNOWNBUG): next layer
is "found no match for symbol '__tuple_impl'" DURING the drain's
conversion of tuple's ctor — args (indices, types, indices, types,
int); the ctor-template deduction fails in the deferred context
(works eagerly: tb3/tb4 pass).  tb7 kernel reproduces.
5 suites green.

## Round 45 (2026-08-15): FLIP cpp20_tuple_converting_element → CORE

FIXED: (1) the trailing-function-pack RETURN-TYPE recorder (gfta
~10016) stamped pack_deduced_types into the FIRST type pack — _Tf
{box}→{int} clobber; now LAST type pack + no-clobber (mirrors the twin
at ~9309; [temp.deduct.call]/1).  (2) apply()'s ambiguous-ellipsis
pack expansion prefers deduction_parameters over lexicographic suffix
match ([basic.scope.temp]/2) — inner/outer same-template instances
cross-substituted (tuple-in-tuple).  tb7+tb2 green → KNOWNBUG FLIPPED
(non-vacuous, 1 assertion).  tb6 (outer-OPERAND same-template nesting)
still fails under documented V1; NOT a committed-test gap (tb6's shape
is interior to ranges tests + V1 doc).
DIAGNOSIS: deduction was PERFECT (gfta-args probe); the corruption was
in SIGNATURE substitution — probe order: match-fail (fargs) → match-try
(whole signatures) → apply-pack (map state at apply time) pinned the
clobber window to gfta 9520..10080.
5 suites green.  RANGES: base.cpp STILL drops main — next probe needed
(fresh error, round 46).

## Round 45b (2026-08-15): coverage audit #4

Gap found + closed: tb6 (same-template nesting, operand-side V1
collision) was NOT covered — the round-45 findings claimed "interior
to ranges tests" but base.cpp has no tuple<tuple<int>>(int) shape (its
converting-element path = tb2, now FIXED).  NEW KNOWNBUG
cpp20_tuple_nested_same_template (clang-runtime-verified; desc points
at the V1 structural fix and the round-45 deduction_parameters
precedent).  AUDIT LESSON: "interior to X" claims must be verified by
grep against the covering test's source, not assumed from the arc's
history.
All other knowns covered: ranges×2, regex-solver, kind-mismatch
(parked), V1-operand (new).  Census: 5 KNOWNBUGs.

## Round 46 (2026-08-16): out-of-line member class templates + ranges layer map

FIXED: out-of-line member-class-template definitions ([temp.mem]/1 +
[class.nest]/1) — previously silently skipped ("not supported yet",
convert_template_declaration ~3531); take_view::__sentinel<true>{}
died "struct nil still incomplete" and killed the TU.  Graft: body
onto the in-class member declaration in the OUTER template's parse
tree; member params = flattened list's trailing entries.  19-line
kernel sv1 (g++/clang) → CORE cpp17_member_class_template_out_of_line.
5 suites green.
RANGES MAP (te-kernels, /tmp): te2 take(3) alone → PASSES, main
intact.  te3 (the pipe) → main dies in anon-take::operator() at
`take_view(__range, __n)` CTAD (line 234, stmt-tracer pinpointed);
throw is message-less and NOT any instrumented bare-throw site.
SECOND wave (post-main): closure_t default-ctor synthesis chain
resolves pf() → tuple::tuple<> — genuinely ill-formed instantiation
contained by drain BUT [class.default.ctor]/4 says never define
un-odr-used implicit default ctors — eager synthesis remains a latent
hazard (contained; revisit if it surfaces).
NEXT (round 47): the take_view CTAD layer at te3 line 234.

## Round 47 (2026-08-17): CTAD paren-aggregate layer fixed

FIXED: single-argument parenthesized aggregate init after CTAD
([over.match.class.deduct] + [dcl.init.general]/16.6.2.2) — the
deduced `take_view<int>(3)` fell into the explicit-cast path ("invalid
explicit cast").  Fix scoped THREE ways after two regression rounds:
(1) #ctad_deduced flag only (unscoped reshape broke map_piecewise with
a goto-symex assign_from_struct ABORT — downstream initializer paths
assert FULL member lists, no [dcl.init.aggr]/5 padding); (2) single
data member only; (3) same/derived-type operand keeps the copy path.
cvise fleet cv47: te4 244→13 lines in ~8 min (typecheck-phase
criterion).  CORE cpp20_ctad_paren_aggregate_single (g++/clang).
VACUITY LESSON REPEATED: cd3/cd5/cd6 hand-kernels "passed" VACUOUSLY
(dropped main, VERIFICATION SUCCESSFUL with 0 assertions) — mid-round
triage must run the drop-check, not just the verdict.
5 suites green.  NEXT LAYER (te4 still drops): "invalid implicit
conversion from 'int[1]' to 'int'" — take_view<int[1]> instantiated
with the REFERENCE stripped (decltype(declval<R>()) should give
int(&)[1]; cd3 hand-kernel of that shape passes, so context-specific).

## Round 48 (2026-08-17): aggregate deduction candidate + decay

FIXED: [over.match.class.deduct]/1.8 aggregate deduction candidate —
deduce through data-member declared types with [temp.deduct.call]/2
decay (array→pointer etc.); dependent-alias members are non-deduced
contexts.  take_view<int[1]>→take_view<int*>.  Plus [dcl.init.aggr]/2.2
base-element routing via cpp_constructor for single base-typed CTAD
args (iv2 probe found it; braced-variant iv2 ALSO exposed
"unexpected expression: struct" via the RETURN-value path — separate,
shallower issue, superseded by the paren routing for the ranges shape).
cvise cv48: te4→16 lines in ~9 min.  CORE
cpp20_ctad_aggregate_deduction_decay (g++/clang).  te4 fully converts.
5 suites green.
NEXT LAYER (te3, cvise cv49 → /tmp/iv1.cpp 164 lines; minimal probe
/tmp/iv3.cpp 29 lines clang-verified): the __invoke chain —
"unexpected expression: signedbv": expanding `A()...` (functional-cast-
over-pack in decltype trailing returns) substitutes the RAW ELEMENT
TYPE for the whole cast expression; downstream expr typecheck chokes,
__invokable_r::_Result never forms, main dies.  Root per
[temp.variadic]/5: A→int in `A()` must yield the functional cast
`int()`.  Fix site to find: the walker that replaces cpp_name subs
with element types inside CALL/cast expressions (likely
replace_type_pack_ref's `s = elem` on expression subs, or the gfta
trailing-return expander).

## Round 49 (2026-08-18): functional-cast-over-pack + by-value decay

FIXED: (1) [expr.type.conv]+[temp.variadic]/5 — raw-type CALLEE slots
(from expanding `A()...`) re-formed as explicit-constructor-call in
typecheck_side_effect_function_call; iv3/iv4/iv5 kernels green, CORE
cpp11_functional_cast_pack_alias (21-line, g++/clang).  (2)
[expr.type]/1+[temp.deduct.call]/2 — by-value deduction strips the
reference wrapper (incl. ref-marked ARRAY, which is_reference alone
misses — the `ref_array` form!) before array decay, pack + scalar
paths.  iv1 (164-line cvise) fully converts.  5 suites green.
TE3 REMAINING LAYER: `__invoke` no-match with fargs (struct, array,
array) inside __invokable_r<void, take, REF-ARRAY> — the top-level
_Args binding at the CLASS level (invoke_result_t<closure,int(&)[1]>
via operator|'s DECLARED types) keeps the ref-array; __try_call →
declval<_XArgs>()... → __invoke deduction fails.  NOTE te3/base.cpp's
shape uses declval (not A()) here — the declval-forwarding chain into
pf::operator() is the next dig.  Kernels: iv1 CLEAN now; need a fresh
kernel of the declval chain (iv6, round 50).

## Round 50 (2026-08-18): trailing value-init; te3's silent throw isolated

FIXED: [dcl.init.aggr]/5 trailing value-initialization in the CTAD
paren-aggregate route (gate relaxed 1→≥1 data member; the round-47 map
abort was from the UNSCOPED variant, not the padding — verified by
canary).  CORE cpp20_ctad_aggregate_trailing_valueinit (g++/clang).
cvise cv50 → /tmp/iv7.cpp (189 lines) now converts.  5 suites green.
TE3 BLOCKER REMAINS — precisely characterized: anon-take::operator()'s
conversion throws int with (a) NO message even under DBG2 passthrough,
(b) NO instrumented bare-throw site firing, (c) no nested
convert_function (cf-enter) and no mem-init (mi-zero) in between —
the throw originates between counted_iterator::operator* conversion
and the catch, i.e. inside the take_view/closure_t class-instantiation
machinery during the `__range_adaptor_closure_t(__bind_back(...))`
expression — an error()-adjacent throw whose message is eaten by a
non-sfinae null-handler window (candidates: declarator-converter
error-count games, instantiate's has_unassigned at ~3232 with
error()-context that my scanner skips).  ROUND-51 PLAN: instrument
error()-ADJACENT throws in cpp_instantiate_template.cpp +
cpp_declarator_converter.cpp specifically, or bisect by wrapping
instantiate_template with a catch-print-rethrow.
NOTE: real <ranges> test (cpp20_ranges_basic_libcxx) blocked on
DIFFERENT layers (atomic header noise + same_as no-match) — the pipe
KNOWNBUG driver and the real-header test have diverged; treat
separately when te3 clears.

## Round 50b (2026-08-18): coverage audit #5

Gap found + closed: iv2 (braced base-element aggregate CTAD,
`closure(takeish{n})`) — round-48 findings called it "separate,
shallower, superseded"; it is STILL a hard rejects-valid failure
("unexpected expression: struct" via the return-value CTAD hook) with
no committed test → NEW KNOWNBUG cpp20_ctad_braced_base_element
(clang-runtime-verified).  AUDIT LESSON (recurring): "superseded/
shallower" notes in findings are DEFERRALS, not resolutions — each
audit must re-run such kernels.
All other knowns covered: ranges pipe (te3's silent-throw layer
interior to it), ranges basic (real-header divergence: atomic noise +
same_as — interior), regex-solver, kind-mismatch (parked), V1-operand.
Census: 6 KNOWNBUGs.

## Round 51 (2026-08-18): FLIP cpp20_ctad_braced_base_element → CORE

FIXED (3 sub-defects): (1) [dcl.init.aggr]/4.1 whole-base copy in
cpp_constructor's aggregate-with-bases branch — member-wise splice left
the base NONDET (wrong-code; iv3 assertion caught it — round 48 had
validated conversion-only, the drop-check-vs-verify lesson AGAIN);
(2) deduce_class_template_arguments skips already-typed args (the
4790 call re-route pre-typechecks; struct_exprt has no second-round
handler); (3) the re-route wraps args already_typechecked + the ecc
base-element detection unwraps before inspecting.  iv2+iv3 both green
non-vacuous.  5 suites green.  Census 5.
TE3 (task 2) NOT STARTED this round — the silent-throw instrumentation
plan stands (error()-adjacent throws in cpp_instantiate_template +
cpp_declarator_converter, or catch-print-rethrow around
instantiate_template).

## Round 52 (2026-08-18): te3's silent throw TRIANGULATED to V1

No src changes (probe-only round).  DIAGNOSIS COMPLETE:
- RAII uncaught_exceptions() tracers (instantiate_template + resolve)
  — a reusable probe-kit addition: prints the frame an exception
  ESCAPES from, no per-site instrumentation.
- Escape chain: innermost failing resolve = `__invoke [take-fn, array,
  ARRAY]` — the third arg should be INT (get<0>(tuple<int>) from
  __bind_back_op's `invoke(__f, __args..., get<_Ip>(__bound_args)...)`)
  — the get-expansion mis-substitutes under the OUTER tuple's live
  maps.  Then __try_call → _Result → enable_if::type → invoke_result_t
  alias throws out of operator|'s conversion → main dies.
- iv8 kernel (dual pack expansions in one decltype arg list, 42 lines,
  g++/clang): PASSES once given a body — dual expansion per se is
  FINE.  KERNEL LESSON: declaration-only helpers make no-body FAILURES
  that look like drops — give kernels bodies.
- The failing ingredient is get<I>(b) where b's type is the SAME
  template nested (tuple<int> inside tuple<take, tuple<int>>) — the
  V1 operand-side collision, ALREADY covered by KNOWNBUG
  cpp20_tuple_nested_same_template (still failing identically).
CONCLUSION: cpp20_ranges_pipe_invoke_drop is BLOCKED ON V1.  The
structural fix (exact scope-qualified parameter resolution replacing
suffix matching in template_mapt apply/build) is now the campaign's
single highest-value target: it unlocks the pipe KNOWNBUG + the V1
KNOWNBUG together.  Round 53 = the V1 arc (its own multi-round effort;
design in doc/architectural/cpp-frontend-review-2026-06-24-*.md).

## Round 53 (2026-08-20): FLIP cpp20_tuple_nested_same_template → CORE (V2 increment)

Read the V1 doc FIRST — it recorded increments 1-2 (nearest-scope
disambiguation DONE; bridge removal proven non-viable, deferred for
lack of a driving test).  Our new KNOWNBUGs supply that test, and our
shape is pure V2 (same template nested: keys differ only by instance
prefix, so no scope-distance rule helps).
FIXED: at the pseudo-instance → real-instantiation rebuild, hide
foreign same-short-name bindings ([temp.point]/1 + [basic.scope.temp]/2)
while replaying #deduced_packs; saved_map restores on exit.  Kernel
wrong-code → SUCCESS; 5 suites green; doc updated with Increment 3.
DIAGNOSIS TOOLING that cracked it: RAII uncaught_exceptions() tracers +
resolve-sequence stamping (correlate "which resolve failed" with "which
candidates it was offered") — the failing resolve was offered ONLY the
outer signature.
TE3 (ranges pipe) STILL DROPS: same class, next site — "__tuple_leaf
does not uniquely resolve" inside __tuple_impl's COPY ctor conversion
(a synthesized member, so no #deduced_packs to replay: the shadow hook
does not apply there).  Next increment: extend isolation to
synthesized-member conversion (or hide by the CLASS's own parameter
ids at convert_function entry for template instances).
Census 4: ranges pipe, ranges basic, regex, kind-mismatch.

## Round 53b (2026-08-20): coverage audit #6

Checked the two candidates from rounds 46/53:
- SYNTHESIZED-member V2 collision (te3/pipe's current layer,
  `__tuple_leaf does not uniquely resolve` in __tuple_impl's implicit
  copy ctor): hand kernel sy1 (same-template nesting + synthesized copy
  through leaf bases) VERIFIES CORRECTLY — not standalone-reproducible;
  VERIFIED interior to the committed KNOWNBUG cpp20_ranges_pipe_invoke_
  drop (its main.cpp emits exactly that error).  Desc updated to record
  it as that test's coverage.
- [class.default.ctor]/4 eager implicit-default-ctor synthesis (round-46
  note): latent hazard, still no reachable trigger (contained by the
  drain's recovery); same treatment as the round-38 lambda hazard —
  documented, no test, since no observable defect exists to pin.
Census 4: ranges pipe, ranges basic, regex, kind-mismatch — all
committed; no diagnosed problem lives only in /tmp.

## Round 54 (2026-08-20): pipe blocker re-diagnosed (no src change)

METHODOLOGY CORRECTION (important): with the CBMC_DBG2 sfinae
passthrough active, SUPPRESSED probe errors print too — the
`__tuple_leaf does not uniquely resolve` line I recorded in round 53 as
"the next layer" is a BENIGN caught error (the base-name type probe in
the [class.base.init]/7 lowering, sfinae-guarded).  Always confirm a
candidate blocker by running WITHOUT the passthrough (real errors only).
The pipe desc's round-53 status note is therefore imprecise (harmless:
it names an error the test does emit under passthrough).
ACTUAL pipe blocker (unsuppressed): __invoke's overload resolution
fails with args (anon-take, ARRAY, ARRAY) inside __invokable_r at
sfinae depth 9 — the second expansion `get<_Ip>(__bound_args_)...` in
`invoke(__f, __args..., get<_Ip>(__bound_args_)...)` yields the VIEW
(int(&)[1]) instead of the bound `int 3`.  So the class-level non-type
pack `_Ip` / `__bound_args_` expansion is contaminated by the FUNCTION
parameter pack `__args` in the same argument list.  iv8 (hand kernel of
dual expansions incl. class-level non-type pack) PASSES, so the trigger
needs more context (candidate: the closure's inherited-ctor/aggregate
base path putting __bound_args_ in a base subobject, so `get` resolves
against the base's own parameter map).
NEXT (round 55): probe `_Ip` size + `__bound_args_`'s resolved type at
the get<> expansion inside __bind_back_op::operator(); build the kernel
from __bind_back_op + a base-held tuple rather than a plain member.
Census 4 unchanged; 5 suites green (round 53 validation still current —
no src change this round).

## Round 55 (2026-08-20): fold-over-class-pack FIXED; pipe blocker kerneled

Built the base-held kernel family bh1-bh6 (43→32 lines) from the
round-54 diagnosis.  TWO distinct defects separated:
(a) FIXED + CORE cpp20_fold_over_class_pack_in_member: the member-body
fold expander sized packs only from replicated function params or a
UNIQUE pack_size_map entry; a fold over the ENCLOSING CLASS pack with
the member's own pack live matched neither → unexpanded
`cpp_binary_fold` → body dropped.  Now sized from the pack the PATTERN
names, per-element VALUE substitution ([expr.prim.fold]/1-2 +
[temp.variadic]/5, empty-pack identity /3).  g++/clang verified.
(b) NEW KNOWNBUG cpp20_pack_expansion_in_call_with_class_pack (bh3, 39
lines, g++/clang): the CALL-ARGUMENT expansion form — `Op()(a...,
get<Ip>(bound_)...)` with a tup<B...> member — mis-converts the
constructor's mem-init ("invalid implicit conversion from 'signed int'
to 'struct tup'"), dropping the ctor body.  This is the pipe's
remaining blocker; the KNOWNBUG makes it minimal + committed (the pipe
desc's coverage note can retire once this flips).
5 suites green.  Census 5 (4 + the new one; net 0 since the pipe still
needs it).

## Round 56 (2026-08-20): mem-init pack expansion FIXED; member paren-aggregate next

FIXED (committed): [temp.variadic]/5 bare pack-expansion mem-init args
resolve against the materialised parameters (plain name for 1 element,
`b$k` for N>=2).  Diagnosis chain: conv-fail probe showed from=NIL →
mi-entry probe showed the operand is a bare cpp_name with ellipsis=1
STILL SET → the scope lookup finds the plain parameter `b`, so the
one-element expansion just needed the ellipsis stripped.
5 suites green.
REMAINING (KNOWNBUG desc updated): `tup<B...> bound_` initialized from
the single resolved argument needs C++20 paren-aggregate init for a
MEMBER ([dcl.init.general]/16.6.2.2).  Existing coverage: CTAD casts
(rounds 47/50) + aggregate BASES ([class.base.init]/7, round 43);
MEMBERS of aggregate class type with a paren list are not routed, so
implicit conversion int→tup<int> is attempted and fails.  Round 57:
add that route in cpp_constructor's member path (mirror the base
branch), gated to aggregates with no viable constructor, and re-check
the map-piecewise canary (the round-47 abort came from an unscoped
variant of exactly this kind of routing).

## Round 57 (2026-08-20): FLIP cpp20_pack_expansion_in_call_with_class_pack → CORE

FIXED: [dcl.init.general]/16.6.2.2 paren-aggregate initialization of a
MEMBER of aggregate class type — tried BEFORE constructor resolution
(which hard-throws converting the whole list to the member type, so a
post-hoc "if cpp_constructor returned nullopt" branch never ran: first
attempt wasted, lesson = check whether the failing path THROWS before
placing a fallback after it).  Gated: aggregates only
([dcl.init.aggr]/1) + single same/derived-type operand stays
copy-initialization (/16.6.1).  bh1+bh3 green, 5 suites green,
map-piecewise canary green.
Pipe (te3) STILL drops main — next error to be read at round 58 (the
grep in this round hit only preprocessor noise; re-run with the
non-noise filter).
Census 4: ranges pipe, ranges basic, regex, kind-mismatch.

## Round 58 (2026-08-21): pipe blocker re-scoped (diagnosis round, no src change)

RED HERRING RETIRED: the `__tuple_impl` no-match now appears AFTER main's
drop in the output (line 71 vs 16) — it is the POST-main wave (the
never-odr-used empty-pack default construction, the [class.default.ctor]/4
hazard from round 46), NOT main's killer.  LESSON: order the diagnostic
output (grep -n) before attributing a failure to an error message.
main dies SILENTLY inside the invoke_result_t/__invoke_of chain (only the
instantiation stack prints).
KERNELS BUILT (all PASS, ruling their shapes out): bh7 = bh1 + trailing-
return decltype with both expansions; bh8 = bh7 + a full
__invoke/invokable_r/invoke SFINAE chain routed through the closure.
So the remaining trigger needs something none of bh1/bh3/bh6/bh7/bh8 nor
iv1-iv8 has: candidates (in order of suspicion) — the hidden-friend
operator| with concept-constrained parameters (viewable_range /
_RangeAdaptorClosure) driving the SFINAE, tuple_size_v/tuple_element
recursion inside __bind_back_t's base computation, or the
counted_iterator/take_view layer instantiated during the same
expression.
NEXT (round 59): bisect te3 downward with cvise using a criterion that
requires main to DROOP with NO error message before it (i.e. grep -n
ordering: 'could not fully' appears before any 'no match'), which
targets the silent throw directly instead of the post-main noise that
misled rounds 53/58.
Census 4 unchanged; 5 suites green (round 57 validation current).

## Round 58b (2026-08-21): coverage audit #7

STATUS CHANGE checked: the [class.default.ctor]/4 hazard (round 46,
recorded then as "latent, no reachable trigger") is now KNOWN TO FIRE —
round 58 showed the post-main wave instantiating a never-odr-used
empty-pack construction and emitting `no match for symbol
'__tuple_impl'` where a conforming compiler is silent.  So it is a
problem we are aware of, and it needed a coverage decision.
Two hand kernels attempted and BOTH VERIFY CLEAN (no spurious
instantiation): dc1 (inheriting-ctor closure over a base whose variadic
ctor is ill-formed when empty) and dc2 (two-base aggregate closure
built by aggregate initialization — te3's shape).  So it is not
standalone-reproducible; it is interior to KNOWNBUG
cpp20_ranges_pipe_invoke_drop, whose desc already records the
post-main wave (round-58 note).  No new test.
Also confirmed unchanged: the drop itself is silent (no message), so
the pipe test remains the only carrier of that layer too.
Census 4, all committed: ranges pipe, ranges basic, regex,
kind-mismatch.  Nothing diagnosed lives only in /tmp.

## Round 59 (2026-08-21): mechanical reduction + innermost frame identified

MECHANICAL PLAN EXECUTED: cvise with an OUTPUT-ORDERING criterion (main's
drop must appear with NO error line before it; post-main noise allowed)
→ 168 lines, saved as .kiro/reductions/ranges_pipe_sd1_168lines.cpp.
ABLATION: replacing the whole tuple machinery with a trivial holder KEEPS
the silent drop → tuple/__tuple_impl is NOT required (retires that whole
line of investigation).  Hand-repairing the ablated file to satisfy the
clang gate failed (the SFINAE chain needs get<>'s real return shape), so
sd1 remains the artifact.
INNERMOST THROWING FRAME (RAII uncaught_exceptions tracers on resolve +
instantiate_template): `X-res take_view` — i.e. resolving take_view (the
CTAD/guide path inside anon-take::operator()) throws FIRST; __invoke /
__try_call / _Result / enable_if::type / invoke_result_t / invoke are all
DOWNSTREAM consequences.  Rounds 52/54/58 were reading those downstream
frames.
KERNEL tv1 (guide-based CTAD, array-ref argument, dependent-alias second
member) PASSES → the throw needs more than the guide shape; next
suspects inside resolve(take_view): the `view`/`viewable_range` CONCEPT
constraint on take_view's parameter (sd1 keeps concepts), or
tuple_size_v/enable_view evaluation during the guide's return-type
instantiation.
NEXT (round 60): instrument resolve() to print the throw ORIGIN for
base_name=="take_view" (which sub-call throws: typecheck_template_args,
deduce_class_template_arguments, elaborate_class_template, or the
constraint check), then kernel that specific sub-path.
Census 4; tree clean; suites green from round 57.

## Round 60 (2026-08-21): take_view's throw site narrowed by elimination

Probe campaign on the committed 168-line artifact (sd1), all with RAII
uncaught_exceptions() tracers, definitive ORDERING (innermost first):
  X-res take_view  ← FIRST, then __invoke, __try_call, _Result,
  X-targs enable_if (downstream), enable_if, type, invoke_result_t,
  invoke, operator() ...
ELIMINATED as the origin of take_view's throw:
- typecheck_template_args (traced; fires only later, for enable_if)
- elaborate_class_template (traced; never fires)
- deduce_class_template_arguments (traced; never fires)
- instantiate_template (traced; never fires for take_view)
- ALL 13 message-less `throw 0` sites in cpp_typecheck_resolve.cpp
  (each instrumented; none fires before X-res take_view)
- resolve's all-templates SFINAE throw with base_name=="take_view"
  (targeted probe; never fires)
So the exception enters resolve(take_view) from a DEEPER callee, and it
may not be `int` at all (candidates: a std::string throw like the
round-39 type2name escape, or a throw from typecheck_type /
implicit_typecast / constant folding).
FAILED TECHNIQUE (do not repeat): identifying the type by
std::rethrow_exception(std::current_exception()) inside the RAII
destructor — crashes (rethrow during unwinding).  SAFE alternative for
round 61: wrap the resolve CALL SITE (typecheck_expr's cpp_name path)
in try / catch-by-type (int, std::string, const char*, std::exception,
...) that PRINTS and RETHROWS; no destructor involved.
Census 4; tree clean; suites green from round 57.

## Round 61 (2026-08-21): the 168-line artifact was DEGENERATE — criterion fixed

Chased take_view's throw to its site by instrumenting EVERY `throw 0`
(346 sites outside resolve.cpp + 43 inside): the firing site is
resolve.cpp's disambiguation error+throw, and with the sfinae
passthrough its message reads:
  "symbol 'take_view' does not uniquely resolve:
     constructor struct ranges::take_view ()
     constructor struct ranges::take_view (struct ranges::take_view)"
at sd1.cpp:159 — whose text is `take_view;` INSIDE a member function.
cvise had rewritten the driver so that a bare class name appears as a
statement.  That is an EMPTY DECLARATION ([dcl.dcl]/3: a
simple-declaration with no declarator is ill-formed unless it declares a
class/enum): clang only WARNS (-Wmissing-declarations), g++ ERRORS
(-fpermissive).  So CBMC's diagnosis is CONFORMING and the artifact is
INVALID — sd1 (and by extension the round-59/60 "innermost frame"
conclusions about take_view) is a degenerate harvest, not the pipe bug.
CRITERION FIX (the actual deliverable): the reduction gate must require
BOTH compilers to accept with NO warnings —
  clang++ -std=c++20 -Werror -fsyntax-only  AND
  g++     -std=c++20 -Werror -fsyntax-only
in addition to the runtime gate and the output-ordering rule.  My cvise
notes already warned about degenerate harvests; the warning-free gate is
the concrete guard and must be in every future criterion.
STATUS: rounds 59-61's take_view line of investigation is RETIRED.  The
genuine pipe blocker is still the silent main-drop in te3/the committed
KNOWNBUG; sd1 must be re-reduced under the corrected gate (round 62).
Kept: the ablation result from round 59 (tuple machinery NOT required)
is independent of the degenerate statement and still stands.
Census 4; tree clean (all probes reverted); suites green from round 57.

## Round 62 (2026-08-22): VALID re-reduction + real signature found

Corrected gate (clang -Werror -fsyntax-only + trap-prelude RUN +
drop-before-any-error ordering) VALIDATED BOTH WAYS: accepts te3,
REJECTS the round-59 degenerate artifact.  g++ cannot be part of this
gate (the driver uses clang builtins: __is_lvalue_reference etc.).
cvise → 191 lines, committed as
.kiro/reductions/ranges_pipe_valid_191lines.cpp (valid under the gate).
FIRST suppressed error in the valid artifact (a NEW signature, not the
retired take_view line):
  invalid implicit conversion from '<<type:>>' to
  'ranges::range_difference_t<ptr_signed_int>'
with the instantiation chain showing an ARGUMENT-PACK BLEED:
  invoke_result_t with <anon-take, int*, int>      <-- correct
  __invoke_of    with <anon-take, int*, int*>      <-- second element
                                                      REPLACED by the first
  __invokable_r  with <void, anon-take, int*, int*>
  __try_call     -> no match (args: int)
So substituting a pack through the alias chain
(invoke_result_t -> __invoke_of -> __invokable_r) duplicates the FIRST
element instead of preserving the element list; the resulting `<<type:>>`
(empty type) then fails conversion to the guide's
range_difference_t<_View> parameter, and main is dropped.
NEXT (round 63): kernel it — alias template forwarding a pack into a
class template with >=2 HETEROGENEOUS elements (ptr + int), assert
arity/order after substitution; then fix in the alias-substitution path
(template_map apply for alias templates / typecheck_template_args'
alias expansion).
Census 4; tree clean; suites green from round 57.

## Round 63 / audit #8 (2026-09-03): pack bleed KERNELED → new KNOWNBUG

Round-62's signature is now standalone: kernel ab2 (27 lines, g++ and
clang -Werror clean, runs clean natively) DROPS MAIN — committed as
KNOWNBUG cpp20_invoke_chain_pack_forwarding.  Suppressed errors: "no
match for symbol 'operator()'" (inside __invoke's trailing return) and
"no match for symbol 'try_call'".  Shape: heterogeneous pack (int*, int)
forwarded through declval<XA>()... in a static member's decltype and
then declval<A>()... in __invoke's trailing return.
NEGATIVE RESULT: the simpler ab1 (alias template forwarding a pack into
a class template, arity assertion) PASSES — so the bleed needs the
DECLTYPE/trailing-return double indirection, not merely an alias chain.
VACUITY CATCH: ab2 first appeared to "pass" (VERIFICATION SUCCESSFUL) —
it was vacuous (main dropped, 0 assertions).  The standing rule caught
it; kernels must always be checked with --show-properties.
Census 5: ranges pipe, ranges basic, regex, kind-mismatch, invoke-chain
pack forwarding (the pipe's minimal blocker).

## Round 64 (2026-09-03): pack-bleed chain traced to an OVERWRITE (no src change)

Measured on KNOWNBUG cpp20_invoke_chain_pack_forwarding (ab2, 27 lines):
1. The failing resolve is `operator()` with args (fn, ARRAY, ARRAY) — the
   second element should be `int`.
2. The existing expander DOES cover this shape: expand_call_argument_packs
   fires for `declval<A>()...` / `declval<XA>()...` (matched=type,
   base=A / base=XA) — so the expansion LOGIC is fine.
3. But at expansion time the binding is already wrong:
   pack_args_map[template::8::A] = [pointer, pointer] (element 2 = a copy
   of element 1), likewise template::9::A.
4. Deduction itself is CORRECT: the forwarding-reference recorder pushes
   (pointer, signedbv) for `invoke(fn{}, arr, 3)` — verified by probe.
So a LATER write corrupts pack_args_map (or build() rebuilds it from an
already-corrupted flat argument list).  Prime suspects, in order:
  a) template_mapt::build() computing pack elements from the instance's
     flat ID_C_template_arguments when those args are themselves wrong;
  b) build_template_args' placeholder expansion (round-45 area) emitting
     <F, int*, int*>;
  c) a second deduction round for try_call/__invoke overwriting the entry
     (the probe showed two later fwd-pushes of `pointer` from `array`).
NEXT (round 65): probe pack_args_map WRITES (add a debug setter or print
at each assignment site keyed on short name "A") to catch the overwriting
site directly, rather than inferring from reads.
MY SPECULATIVE FIX REVERTED: adding a second call-argument expander to
apply(exprt) changed nothing (the existing decltype path already
expands) — do not re-add; the defect is upstream of expansion.
Census 5; tree clean; suites green from round 57.

## Round 65 (2026-09-03): overwriter hunt — three sites eliminated

Instrumented (by hand, after two scripted attempts broke the build:
misleading-indentation + std::move-into-print) the three suspects from
round 64, printing on WRITE, filtered to short name "A", on KNOWNBUG
cpp20_invoke_chain_pack_forwarding:
- template_mapt::build()'s `pack_args_map[pack_id] = pack_types`  -> NEVER fires
- gfta recorder at ~9397 (twin, no-clobber)                       -> NEVER fires
- gfta recorder at ~10079 (last-type-pack, no-clobber)            -> NEVER fires
So the [pointer,pointer] binding for A is written by one of the REMAINING
sites; next round instrument these, in order:
  cpp_typecheck_resolve.cpp:8254 and :8667 (guess_template_args' class-
    template-id pack recorders — most likely, since __invokable_r<void,
    F, A...> binds its pack from a template-id),
  :5378, :5488, :4724, :1553,
  cpp_instantiate_template.cpp:1749, :3517, :3629, :3754,
  cpp_typecheck_method_bodies.cpp:186, :247.
TOOLING NOTE: script-inserted probes around `X = std::move(Y);` and
inside un-braced `if` bodies keep breaking the build (-Werror); for write
instrumentation prefer ONE hand edit per site, printing the SOURCE vector
before the move.
Census 5; tree clean (probes reverted, grep 0); suites green from
round 57.

## Round 66 (2026-09-03): two more eliminations + a correction

On KNOWNBUG cpp20_invoke_chain_pack_forwarding (hand-written probes):
- guess_template_args' pack recorders (resolve.cpp:8254, :8667): NEVER fire
- template_mapt::build()'s SECOND pack write (template_map.cpp:2307):
  NEVER fires (the first, :2423, was already eliminated in round 65)
- apply(typet)'s `if(type.id() == ID_decltype) expand_call_argument_packs`
  branch: NEVER REACHED for this kernel (probe counted 0 calls)
CORRECTION to round 64: the "exp-arg matched=type base=A/XA,
pack_args_map[A]=[pointer,pointer]" observation therefore did NOT come
from this kernel — it must have come from the 191-line pipe artifact
(vd1) that was also being run that round.  So for the KERNEL the story is
different and simpler: the trailing-return decltype is NOT substituted
via apply(typet) at all, and no pack_args_map entry for "A" is ever
written.  The failing resolve sees (fn, ARRAY, ARRAY) because the
expansion never happens: `declval<A>()...` is left with its ellipsis and
both arguments come from the same unexpanded pattern.
NEXT (round 67): find the route that DOES process __invoke's trailing
return for this kernel — probe guess_function_template_args at its
`template_map.apply(function_type)` call (print the return type's id and
whether pack_args_map is empty at that moment); the likely answer is that
the pack is bound only in type_map (scalar) with NO pack_args_map entry,
so every expander that keys on pack_args_map is a no-op.  If so the fix
is to record the deduced function-parameter pack in pack_args_map on this
path (mirroring rounds 45/49) rather than to touch the expanders.
LESSON: when two inputs are under investigation in one round, tag every
probe line with the input file, or run them in separate commands.
Census 5; tree clean (grep 0); suites green from round 57.

## Round 67 (2026-09-03): PLUMBING BUG found; corrected data pins the corruption

CRITICAL PROCESS BUG: from round 65 onward I ran probes as
`../../../build/bin/cbmc` from regression/cbmc-cpp — that path does NOT
resolve (the binary is ../../build/bin/cbmc from there); `timeout`
reported "No such file or directory" on stderr, which my greps discarded.
Every probe run in rounds 65-66 therefore produced NO OUTPUT for
mechanical reasons, and the "eliminations" recorded there
(build()'s two writes, gfta recorders 9397/10079, gta 8254/8667,
apply(typet)'s decltype branch not reached) are VOID — they were never
actually measured.  RULE: always use the ABSOLUTE binary path in probe
commands (test.pl runs are unaffected: it resolves its own -c argument
from the suite directory).
CORRECTED MEASUREMENT (absolute path, KNOWNBUG
cpp20_invoke_chain_pack_forwarding), template_mapt::build calls:
  build for `invoke`      : params <F, PACK:A>      args (fn, pointer, signedbv)   CORRECT
  build for `invokable_r` : params <anon#1, F, PACK:A> args (void, fn, pointer, POINTER)  WRONG
So the pack is deduced and bound correctly for `invoke`, and the
corruption happens when the ARGUMENT LIST for
`invokable_r<void, F, A...>` is formed inside
`invoke_result_t<F, A...>`: expanding `A...` there emits the pack's
SCALAR convenience binding (element 0, the pointer) TWICE instead of its
two elements.  This is the [temp.variadic]/5 class-template-argument
expansion path (typecheck_template_args / apply's template_args handling)
seen in rounds 42/45 — but for a pack referenced through an ALIAS
template's argument list.
NEXT (round 68): probe typecheck_template_args' expansion gate for
invokable_r with the correct path (does the gate open? are the
referenced_packs found?), then fix so the alias's argument list expands
element-wise.
Census 5; tree clean (grep 0); suites green from round 57.

## Round 67b (2026-09-03): coverage audit #9

Checked whether round 67's mechanism (expanding `A...` in an ALIAS
template's argument list emitting the scalar binding twice) has a SIMPLER
uncovered manifestation: kernel al1 — `template<class F, class... A>
using holder_alias = holder<F, A...>;` used as `holder_alias<F, A...>::
arity` inside a function template, heterogeneous pack (int*, int),
non-vacuous (1 assertion) — VERIFIES CORRECTLY (arity 2) under both
compilers' -Werror.  So plain alias pack forwarding works; the defect
needs the decltype/`invokable_r` context of the committed KNOWNBUG.  No
new test.
Census 5, all committed and each a distinct problem:
  cpp20_invoke_chain_pack_forwarding  (alias-args pack expansion, 27 lines)
  cpp20_ranges_pipe_invoke_drop       (full driver; same root + post-main wave)
  cpp20_ranges_basic_libcxx           (real-header blockers)
  cpp11_regex_match                   (solver-time variance)
  cpp11_deduced_nontype_kind_mismatch (parked; documented blocker)
Nothing diagnosed lives only in /tmp.  (Note: /tmp kernels from earlier
rounds were cleaned up by the OS; the committed tests and the two saved
reductions in .kiro/reductions carry everything needed.)

## Round 68 (2026-09-03): corruption bracketed to the alias BODY substitution

All probes below used the ABSOLUTE binary path (round-67 rule) on
KNOWNBUG cpp20_invoke_chain_pack_forwarding.  Measured, in order:
- resolve_template_alias(invoke_result_t) RECEIVES correct args
  (fn, pointer, signedbv) and its pack state is A(2).
- the same function INSTANTIATES the alias with correct args
  (type/struct_tag type/pointer type/signedbv).
- apply(typet)'s ambiguous-ellipsis template-argument expansion, when it
  fires, sees the CORRECT pack: template::10::A / template::11::A =
  [pointer signedbv].
- yet template_mapt::build for `invokable_r` receives
  (void, fn, pointer, POINTER) -- element 2 duplicated.
So the duplication happens while the alias's BODY
(`typename invokable_r<void, F, A...>::result`) is substituted -- between
the correct alias instantiation and invokable_r's argument list.  The
expansion loop's INPUT is right, so the next probe must capture its
OUTPUT: print what the ambiguous-ellipsis loop PUSHES for the
invokable_r pattern (and whether a second substitution pass rewrites the
pushed elements).
NEXT (round 69): probe the push site inside apply(typet)'s expansion loop
(the `expanded_args.push_back(wrapped)` for type packs) printing each
emitted element, filtered to pattern name "invokable_r"; then fix.
Census 5; tree clean (grep 0); suites green from round 57.
