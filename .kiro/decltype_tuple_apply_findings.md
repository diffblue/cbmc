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
