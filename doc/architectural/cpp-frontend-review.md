\file

C++ Front-End Architectural Review

# C++ Front-End Architectural Review

**Date:** 2026-05-13
**Scope:** `src/cpp/` — CBMC's C++ type-checker and template machinery.
**Motivation:** 60+ targeted fixes landed on `cpp11-parser-rework-squashed`
in ~3 weeks.  This document steps back from the individual fixes to ask
whether the pattern points to systemic architectural problems that must
be addressed before we declare the front end "solid enough for customers"
— especially given that CBMC itself dog-foods through `goto-cc` at only
**10 of 117 (~8.5%) OK_CLEAN** on `src/util/`.

Standard references throughout are to **N5008** (C++26 working draft).

---

## 1. Executive summary

The recent fixes point out a real need for re-architecting **three**
subsystems.  They are, in decreasing order of structural impact:

| # | Subsystem | Standard anchor | Current state | Evidence |
|---|-----------|-----------------|---------------|----------|
| 1 | **Class-body elaboration** | [temp.inst]/3 | Eager, all-or-nothing | 60% of recent fixes |
| 2 | **Template resolve / SFINAE context tracking** | [temp.deduct]/8 | Implicit, via try/catch | 95 try/catch calls, 24 error-count save/restores |
| 3 | **Overload resolution / target-type threading** | [temp.deduct.funcaddr], [over.match] | Forward-only pipeline | P2 required a two-pass retrofit |

Two more subsystems have smaller (but still meaningful) cleanup opportunities:

- **Template alias handling** ([temp.alias]): no memoization; fixed with
  a thread-local active-set guard (`09e5625681`) but the proper fix is a
  concrete cache keyed on (alias symbol, arg tuple).
- **Point-of-instantiation tracking** ([temp.point]): `instantiation_stack`
  exists but is used inconsistently; POI is an ad-hoc notion rather than a
  first-class attribute of name lookups.

The remaining fixes are mostly **symptoms** of the above subsystems and
would largely vanish once they are addressed.  Concretely: a principled
two-phase name lookup in templates ([temp.res.general]) would remove the
scope-walk retries that account for the majority of recent lookup-related
patches.

The dog-food metric is the right customer-surrogate: customers feed CBMC
real-world C++ headers (STL, MSVC system, libc++), and those headers
exercise the same patterns we currently mis-handle.  **Without re-architecting,
new customer code will keep hitting new symptoms of the same architectural
issues, and each fix will look like another one-off patch.**

---

## 2. Evidence: the fix pattern

Fix-cadence over the last three weeks (commits against
`cpp11-parser-rework-squashed` since `ac830e7ef6`):

```
$ git log --oneline ac830e7ef6..HEAD | wc -l
61 commits
$ git log --oneline ac830e7ef6..HEAD | grep -ciE 'sfinae|template|resolve|instantiate|elaborate|typecheck_compound|deduct'
~40 (~65%)
```

The structural similarity of the fixes is striking.  They fall into four
recurring shapes:

### 2.1 "Wrap the error-emitting code in a silent-throw guard"

Pattern:

```cpp
null_message_handlert sfinae_null_handler;
message_handlert &old = cpp_typecheck.get_message_handler();
cpp_typecheck.set_message_handler(sfinae_null_handler);
exprt e;
try { e = guess_function_template_args(old_id, fargs); }
catch(...) { cpp_typecheck.set_message_handler(old); continue; }
cpp_typecheck.set_message_handler(old);
```

This appears **in at least three different places** in `src/cpp/` and is
encoding, by hand, the "immediate context" rule of [temp.deduct]/8.
Each site chose its own boundary for the guarded region; none of them
propagate the "this failure is a SFINAE failure, not a hard error" fact
to the caller in a structured way.  The count:

```
$ grep -rn "null_message_handlert\|catch(int)\|catch(\.\.\.)" src/cpp/ | wc -l
95
```

### 2.2 "After failure, keep the unresolved cpp_name so the loop continues"

Pattern (from `typecheck_compound_body` for member declarations):

```cpp
typet saved_type = declaration.type();
try { typecheck_type(declaration.type()); }
catch(...) { declaration.type() = saved_type; /* keep unresolved */ }
```

This encodes the principle that a class's member-type failure should not
abort the whole class body — a principle the standard does not state
directly but which follows from [temp.inst]/3 (only declarations are
implicitly instantiated, not definitions).  The pattern fires in three
different positions in one function, all added independently.

### 2.3 "The call failed, try again in a different scope"

Pattern: when a name is not found in the current scope, walk
enclosing/using-bound scopes and retry.  This substitutes for a proper
two-phase lookup per [temp.res.general]/1.

```
$ grep -rn "lookup(.*RECURSIVE)" src/cpp/ | wc -l
6 call sites
$ grep -rn "cpp_scopes.current_scope().lookup" src/cpp/ | wc -l
~30 call sites
```

Each is a case-specific scope walk.

### 2.4 "Bail out at depth N to stop recursion"

Pattern: when recursion cannot converge, cap the depth with a
thread-local counter or active-set.

Examples this month:
- `09e5625681` — `resolve_template_alias` active set (cycle break).
- `424da3ca32` — `alignment()` cycle guard.

These are correct band-aids but indicate the recursion isn't
terminating by *value* (memoization), only by *depth*.  The standard
semantics for template aliases ([temp.alias]) are that an alias-template
specialization is equivalent to its aliased type — which means the
second evaluation of the same alias with the same arguments **must**
produce the same result, so it's a trivial memoization target.

---

## 3. The three structural issues in depth

### 3.1 Class-body elaboration is eager and all-or-nothing

**Standard** ([temp.inst]/3):

> The implicit instantiation of a class template specialization causes
> — the implicit instantiation of the declarations, but not of the
> definitions, of the non-deleted class member functions, member classes,
> scoped member enumerations, static data members, member templates, and
> friends; …
> The implicit instantiation of a class template specialization does not
> cause the implicit instantiation of default arguments or
> noexcept-specifiers of the class member functions.

In other words: **instantiate declarations lazily; definitions only when
needed; member types only when they would be needed.**

**CBMC today:** `cpp_typecheck_compound_type.cpp::typecheck_compound_body`
iterates every declaration in the class body (`Forall_operands(it, body)`)
and fully type-checks each member's declared type up front.  If one
member's type cannot be resolved (e.g. a `common_type_t<duration>` return
in duration's own body — a self-referential metafunction), the exception
propagates out of the loop and the remaining members are silently lost.
The P3a fix (`2e8e74f8ed`) works around this for the specific
`common_type_t<duration>` case but leaves the general pattern untouched.
A non-trivial number of dog-food failures ultimately trace to "a member
of some STL template instance never got added to its `components()`
because elaborating its type failed".

The standard-aligned architecture would be:

1. **Declaration pass**: register every member by base_name + access +
   partial type (retain unresolved `cpp_name` where needed).  This is
   what `[temp.inst]/3` calls "instantiation of declarations".
2. **On-demand pass**: when a caller needs the full type of a specific
   member (for construction, access, overload resolution), resolve it
   then.  Failures here become real errors attributed to the use site.

This would structurally eliminate the entire class of bugs that surface
as "class looks almost-complete, but member X is missing".

**Code sites that need refactor:**
- `src/cpp/cpp_typecheck_compound_type.cpp:1185` (`typecheck_compound_body`)
- `src/cpp/cpp_instantiate_template.cpp:626` (`elaborate_class_template`)
- `src/cpp/cpp_typecheck_method_bodies.cpp` (deferred method-body queue
  is a rudimentary version of the right idea — generalize it).

**Migration cost estimate:** medium.  The deferred-method-body machinery
is already a pattern we can extend.  Member types stored as unresolved
`cpp_name`s need a consistent re-resolution protocol (currently ad hoc).
A 2-3 week full-time effort for the core refactor + ~1 week of fix-out
for tests that relied on the eager behaviour.

### 3.2 SFINAE context is implicit, encoded by handler swaps and catches

**Standard** ([temp.deduct]/8):

> If a substitution results in an invalid type or expression, type
> deduction fails.  An invalid type or expression is one that would be
> ill-formed, with a diagnostic required, if written in the same context
> using the substituted arguments. …
> Invalid types and expressions can result in a deduction failure only
> in the **immediate context** of the deduction substitution loci.

The standard therefore requires the implementation to know, at every
point in the resolver, whether we are inside an immediate context (SFINAE)
or not.  A type-resolution failure in an immediate context is a SFINAE
probe result; outside, it's an ill-formed program.

**CBMC today:** SFINAE is encoded by *saving* the error count before a
call, *swapping* the message handler to a `null_message_handlert`, doing
the call, and restoring on throw or exit.  95 call sites do this by hand
with subtly different boundaries, and at least one class of bugs (P1 tail)
was "the error leaked into user-visible output because the guard was at
the wrong level".

The standard-aligned architecture would be:

1. **RAII guard type** `sfinae_contextt` that represents an immediate
   context.  Construction swaps to a silent handler; destruction restores.
2. **API reshape**: the resolver uses `std::optional<T>` (or an outcome
   type) to signal "substitution failed" explicitly, rather than via
   thrown ints + counted error messages.
3. **Hard errors** that escape SFINAE contexts propagate normally and
   are attributed to the use site, not to the probe.
4. **[temp.deduct]/8's "immediate context" must be delineated at the
   type-level**: certain recursive calls (e.g., instantiating a dependent
   class template) are *not* in the immediate context even if the outer
   call is — see the [temp.deduct]/9 example with lambdas.  The RAII
   guard needs to know when to lift (not just how to enter).

This is the cleanest win in readability and correctness: it would
eliminate the 95 hand-rolled guards, collapse the error-count
save/restore pattern (24 sites), and let the compiler/reviewer see at a
glance which resolver operations are SFINAE-safe.

**Code sites:**
- `src/cpp/cpp_typecheck_resolve.cpp:3750+` — "found no match" emission
  is guarded by an ad-hoc `all_templates` check (`01507a3e6d`) that
  should instead be a proper SFINAE context check.
- `src/cpp/cpp_typecheck_resolve.cpp:180` — per-candidate substitution
  guard.
- `src/cpp/cpp_typecheck_template.cpp:~2011` — `typecheck_type(arg.type())`
  during template-args checking: whether this is SFINAE-safe depends on
  the caller, and there's no way to tell in the current code.
- `src/cpp/cpp_typecheck_function.cpp:505+` — `is_system_header_body` is
  *almost* this concept, but specialized to path-suffix tests.

**Migration cost estimate:** medium-small.  The refactor can land
incrementally — introduce `sfinae_contextt`, convert one call site at a
time, and delete the hand-rolled guards.  Each conversion is a local
change testable by the existing suites.

### 3.3 Overload resolution has no target-type propagation

**Standard** ([temp.deduct.funcaddr]/1):

> Template arguments can be deduced from the type specified when taking
> the address of an overload set …  If there is a target, the function
> template's function type and the target type are used as the types of
> P and A, and the deduction is done as described in 13.10.3.6.

Also [temp.deduct.conv], [over.ics.list], and the initialization-list
conversion rules all require the overload resolver to push the target
type (the P) *into* argument evaluation.

**CBMC today:** `cpp_typecheck_expr.cpp::typecheck_side_effect_function_call`
pre-type-checks every argument in isolation *before* resolving the
callee.  If the argument is `&id_sum` where `id_sum` is a function
template, the in-isolation type-check fails (no fargs to drive deduction)
and the argument is left untyped.  The callee then fails to match.

P2 fixed this by bolting on a *second-pass retry*: after the callee is
tentatively resolved (`probe_fn`), re-resolve each failed argument with
synthetic fargs derived from the callee's target parameter type.  This
works for the specific case but is structurally inverted: target-type
information should flow naturally from callee to arguments on the first
pass, not be reconstructed after the fact.

The standard-aligned architecture would be:

1. **Forward the target type** as a first-class parameter to argument
   type-checking.  The signature becomes roughly
   `typecheck_expr(exprt &, const std::optional<typet> &target)`.
2. When target is present and the argument is a function-address / a
   brace-init-list / an aggregate initializer, drive deduction /
   initialization from it per [temp.deduct.funcaddr], [over.ics.list],
   [dcl.init.list].
3. When target is absent (top-level expression, decltype context), fall
   back to current behaviour.

**Code sites:**
- `src/cpp/cpp_typecheck_expr.cpp:2480` — the pre-typecheck loop.
- `src/cpp/cpp_typecheck_expr.cpp:2533` — `typecheck_function_expr`.
- `src/cpp/cpp_typecheck_expr.cpp:3437` — `typecheck_function_call_arguments`
  already runs *after* the callee is resolved; most target-type-aware
  adjustments can happen here.

**Migration cost estimate:** medium.  The threading is mechanical but
touches every call site.  The win is that we retire the P2 probe-retry
pipeline (`d612fe6dac`) and pick up [temp.deduct.funcaddr] for member
pointers, conversion-function templates, and brace-init-list
initialization at the same time.

---

## 4. Secondary architectural issues

### 4.1 Template-alias memoization

**Standard** ([temp.alias]):  An alias-template specialization is the
denoted type; two specializations with equivalent argument lists denote
the same type.

**CBMC today:** `resolve_template_alias` re-runs `typecheck_template_args`
+ `instantiate_template` on every visit.  When combined with SFINAE
cycles (e.g. `add_rvalue_reference_t<T>` → `void_t<T&>` → resolves T →
re-enter), a naive resolver infinite-loops.  The `09e5625681` active-set
guard breaks the cycle but is not a cache — the result is `empty_typet{}`
rather than the correct alias.  For our filesystem test the conservative
placeholder was enough to make downstream verification succeed, but that
is by luck, not by design.

**Fix:** A real `std::unordered_map<(symbol, full_args_hash), typet>`
cache replacing both the active-set and the re-evaluation.

### 4.2 Point-of-instantiation (POI) is ad hoc

**Standard** ([temp.point]): every implicit instantiation has a
concrete POI used for dependent-name lookup ([temp.dep]) and for error
attribution.

**CBMC today:** `instantiation_stack` tracks current nested
instantiations (used for the "reached maximum template recursion depth"
check) but POI itself is not systematically threaded.  Error messages
often attribute to the template definition location rather than the POI,
which confuses users.

**Fix:** attach POI to every template-instantiated symbol at creation;
use POI rather than the template-definition location for error
reporting.  This also enables proper two-phase lookup (§4.3).

### 4.3 Name lookup in templates is effectively single-phase

**Standard** ([temp.res.general]/1): an unqualified name in a template
declaration is looked up **from where it appears** (first phase, at
template definition), and **if dependent**, looked up again at
specialization (second phase, at POI).  Non-dependent names must bind
at phase 1.

**CBMC today:** lookup happens once, typically at elaboration time, and
there are scattered "retry in current scope" fallbacks to patch over
missed bindings.

**Fix:** classify names at parse time into dependent vs non-dependent
(per [temp.dep]), bind non-dependent names immediately at phase 1, and
defer dependent-name resolution to phase 2 with the instantiation
context available.

### 4.4 `irept` sharing discipline under template recursion

**Not a standard issue**, and on re-examination *not an active
source of bugs either*.

When this review was first drafted I hypothesised that the two
`sharing_treet::detach()` SIGSEGVs seen during the session were the
result of shallow-copy save-restore races against CBMC's
copy-on-write `irept`.  A closer look after the short-term
roadmap's item 3 (audit) ran the matter down to the ground:

1. The `detach()` crash in `c_qualifiers_t::write` was a **stack
   overflow** (on the function prologue instruction
   `mov %rdi, 0x8(%rsp)` — a spill, not a dereference) caused by
   unbounded mutual recursion in `resolve_template_alias`.  Fixed
   deterministically by commit `09e5625681`'s active-set cycle
   break.

2. The `detach()` frames attributed to `convert_non_template_declaration`
   were actually a **null-pointer dereference** on an empty
   `name().get_sub()` in the trailing-return-decltype path — a
   parser-output precondition violation.  Fixed by commit
   `df5f5d955e` with an explicit `empty()` guard.

3. The only remaining `typet saved_type = declaration.type(); try {
   typecheck_type(…); } catch(…) { declaration.type() = saved_type;
   }` pattern in the tree
   (`cpp_typecheck_compound_type.cpp:1322`) turns out to be safe:
   `typecheck_type` goes through `detach()` on every write path, so
   the shallow copy in `saved_type` observes the pre-detach `dt*`
   and cannot be corrupted by the inner mutations.

There is therefore no concrete bug class here to retire as part of
the short-term plan.  The COW discipline is holding up; when new
crashes appear, the first question is still "is this stack
exhaustion or a real null-deref?", answered quickly by running in
gdb and decoding the faulting instruction.  If a future bug *does*
trace to shallow-copy races, the fix would be a `deep_copy()`
helper on `irept` at the specific call site, not a tree-wide
refactor.

---

## 5. Metrics

### Current dog-food pass rate

`src/util/` (117 files) with `goto-cc` + plain verification:

```
OK (clean):  10  (8.5%)
OK (noisy):   4  (3.4%)
FAIL:       103 (88.0%)
CRASH:        0  (0%)
```

Given that `src/util/` is *CBMC's own code* using only common C++14/17
features (STL containers, templates, RAII), the 88% FAIL rate is a
strong signal that customer code is going to surface comparable
failures.

### Recurring errors in the `--expand` FAIL set

A rough histogram of the dominant failure messages (after this turn's
fixes):

```
 ~42  unordered_map<...> cascade            → partial class elaboration (§3.1)
 ~35  'char [N]' to basic_string mismatch   → initialization with target type (§3.3)
 ~11  __stoa variadic deduction             → fixed via system-header null handler; symptom of §3.2
   8  'swap' overload set ambiguity         → phase-1 lookup (§4.3)
   2  prvalue materialization               → [class.temporary]
   2  range-for custom iterator             → non-dependent name lookup
  ~3  misc
```

The top two classes of failures are direct consequences of the two
highest-impact architectural issues (§3.1 class-body elaboration, §3.3
target-type propagation).  Closing those would almost certainly move
the OK rate from ~12% to ~50%+ with no additional one-off fixes.

---

## 6. Recommended roadmap

### Short term (2–4 weeks, no architectural changes) — **in progress**

- ✅ **Consolidate SFINAE guards behind a single `sfinae_contextt`
  RAII type (§3.2 first half).**  Landed in commit `7160102bc3`.
  Retires ~20 hand-rolled `null_message_handlert` + error-count
  save/restore patterns across 8 files.  Every converted site
  carries a comment citing the standard clause the guard
  implements ([temp.deduct]/8, [temp.constr.atomic]/3,
  [expr.prim.req.*]/1, [over.ics.user], [expr.unary.noexcept]/3).
- 🟡 **Add a `template_alias_cachet` (§4.1).**  Attempted; regressed
  three CORE tests because CBMC's `irept` argument lists are not
  scope-agnostic and a thread-local cache keyed on
  `(alias, full_args)` returns stale types from a prior scope.
  Reverted to the minimal cycle-break from `09e5625681` with an
  expanded comment; proper scope-keyed memoization is deferred to
  the medium-term lazy-elaboration work (commit `2d0e466bd7`).
- ❌ **Audit and patch the shared-irep save-restore sites (§4.4).**
  On re-examination the hypothesised bug class doesn't exist —
  CBMC's COW discipline holds up and the two recent `detach()`
  SIGSEGVs were stack exhaustion (fixed by `09e5625681`) and a
  null-deref (fixed by `df5f5d955e`), neither sharing-related.
  See §4.4 for the details; no action taken.

Net short-term effect: one retired concern (SFINAE hand-rolls), one
refactor deferred with explicit rationale, one hypothesis
falsified.  All CORE + KNOWNBUG regressions green; MSVC
preprocessed headers still 26/26.  The dog-food `--expand`
baseline is unchanged (10 OK_CLEAN / 4 OK_NOISY / 103 FAIL / 0
CRASH) — the short-term consolidation was about architectural
hygiene, not pass-rate movement; that belongs to the medium-term
work below.

### Medium term (1–3 months)

- **Lazy class-body elaboration (§3.1).**  The central refactor.
  Instantiation produces *declarations*, and a new
  `cpp_typecheckt::ensure_member_complete(struct, base_name)` call
  resolves each member's full type on demand.  This is the single
  change that would most change the dog-food pass rate.
- **Target-type threading in overload resolution (§3.3).**  Retire the
  P2 probe-retry pipeline in favour of a `typet target` parameter on
  arg type-check.  Pick up [temp.deduct.conv] and brace-init-list
  conversions for free.
- **Formal SFINAE context propagation (§3.2 second half).**  Change
  resolver return types from thrown-int to `std::optional<exprt>` (or
  an outcome type) with SFINAE contexts explicit.

### Long term (3–6 months)

- **Two-phase lookup with POI (§4.2, §4.3).**  Classify names as
  dependent vs non-dependent at parse time, bind non-dependent names at
  phase 1, track POI for phase 2.  This is the deepest change but
  unlocks correct handling of a large class of C++ idioms (base-class
  member lookup, unqualified dependent calls, etc.) that currently work
  only by coincidence.

### What to do in the meantime

Keep landing targeted fixes — but **every targeted fix must cite the
standard section it implements** (as the last batch do, e.g.
`[temp.deduct]/8`, `[temp.deduct.funcaddr]`, `[temp.inst]/11`).  When a
fix recurs in spirit (e.g. "catch and continue" guards) file it against
this document so we know the debt is accumulating in one spot.  When the
short-term consolidations above land, targeted fixes against the
consolidated primitives replace N scattered one-offs cleanly.

---

## 7. What this isn't

- **Not a call to rewrite the front-end.**  The parser, most of the
  type-checker for non-template code, the declarator converter, and the
  GOTO-conversion path downstream are solid.  The issues above are
  concentrated in the *template* machinery and the *compound-body
  elaboration* code path.
- **Not a call to freeze targeted fixes.**  Customer code needs CBMC to
  work *now*, and targeted fixes compound in improving pass rates.  The
  argument is that the ROI inverts past a certain point: after ~60 small
  fixes, the next 60 should be fewer, larger, and structural.
- **Not prescriptive on implementation detail.**  Each subsystem has
  several possible refactoring shapes; the point of this doc is to
  agree that they *need* refactoring and to align on priorities.

## 8. Validation criteria for "solid enough for customers"

A customer who compiles typical C++14/17 code (STL, small-to-medium
templates, library headers) should see CBMC succeed without hitting
front-end bugs.  Concrete gates:

1. `src/util/` dog-food: **≥ 80% OK_CLEAN** on `--expand` (today: 8.5%).
2. MSVC preprocessed headers: **26/26 PASS** (today: 26/26 — ✓, but only
   after this turn's fixes — and the margin is thin).
3. Linux CORE + KNOWNBUG regressions: **100% green** (today: ✓).
4. macOS preprocessed headers: **7/7 PASS** (today: 6/7 — blocked on
   libstdc++ coroutines work, out of scope).
5. No `null_message_handlert` / `catch(int)` / `catch(...)` SFINAE
   hand-rolls outside the new `sfinae_contextt` primitive.
6. No dog-food CRASH (today: ✓ — keep it that way).

Gate 1 is the real target.  Hitting it requires the medium-term work
(§6).  Gates 2–4 are maintenance; today's pass is thanks in part to
targeted fixes that the re-architecting should preserve as no-ops.
