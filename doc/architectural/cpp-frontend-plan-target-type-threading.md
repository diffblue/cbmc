\file

Detailed plan: target-type threading in overload resolution

# Detailed plan: target-type threading

**Owner:** — (to be assigned)
**Status:** Proposed
**Parent document:** `doc/architectural/cpp-frontend-review.md` §3.3, §6 (medium term, target-type threading)
**Standard anchors:** N5008 [temp.deduct.funcaddr], [temp.deduct.conv],
[over.ics.list], [dcl.init.list]

## 1. Motivation

Three standard-specified deduction/conversion paths all require the
resolver to know the *target type* when typechecking an argument:

1. **[temp.deduct.funcaddr]/1** — `apply(&id_sum, 3, 4)` where
   `id_sum` is a function template and the parameter is a function
   pointer.  The template arguments are deduced from the target
   function pointer type.

2. **[temp.deduct.conv]/1** — conversion function template arguments
   are deduced by comparing the return type against the required
   conversion target.

3. **[over.ics.list]** + **[dcl.init.list]** — brace-init-list
   conversions depend on the target type.  `f({1,2,3})` where `f`
   takes `std::vector<int>` requires matching `{1,2,3}` against
   `initializer_list<int>`.

CBMC's pipeline is forward-only: `typecheck_side_effect_function_call`
pre-typechecks every argument in isolation *before* resolving the
callee.  For each of the three standard cases above, this order is
backwards — the argument needs the callee's parameter type to
typecheck correctly.

### Existing workarounds to retire

- `deduce_function_address_args_from_target` (commit `a5a4b9f156`,
  refactored from `d612fe6dac`): a probe-and-retry helper that
  resolves the callee first with empty fargs, reads back parameter
  types, then synthesises fargs matching the target and re-resolves
  each deferred argument.  Covers [temp.deduct.funcaddr] for the
  plain function-pointer case.  Does **not** cover
  [temp.deduct.conv] or [over.ics.list].

- Scattered `implicit_typecast` calls in
  `typecheck_function_call_arguments` (`cpp_typecheck_expr.cpp:3437+`)
  that handle brace-init-list → `initializer_list` conversion for
  already-typed arguments.  These run *after* the argument is
  typechecked in isolation, so they can only fix up the final type
  — they cannot participate in overload resolution.

### Dog-food pressure

From `ci-failures-2026-05-13.md` the 35 "`char [N]` to basic_string
mismatch" failures are a family of target-type-driven conversions
that the forward-only pipeline handles via post-hoc repair
(`standard_conversion_sequence` in `cpp_typecheck_conversions.cpp`
already has a narrow `char[N]` → `basic_string` path).  A principled
target-type threading would let the string constructor's
`const char*` parameter drive the argument typecheck from the
start.

Closing this class of failures is projected to move the dog-food
`--expand` pass rate by another ~20 percentage points on top of
the lazy-elaboration baseline, taking us roughly from target 50%
(post-lazy) to ~70% OK_CLEAN.

## 2. Design

### 2.1 Option A — explicit target-type parameter on `typecheck_expr`

```cpp
void typecheck_expr(exprt &expr) override;                    // C compat
void typecheck_expr(exprt &expr, const typet &target);        // C++ only
```

The overload with target is called when the caller has a specific
destination in mind (initialiser for a variable of known type, an
argument bound to a parameter of known type, the RHS of an
assignment, etc.).  The no-target overload delegates to the other
with `empty_typet{}`.

Inside typecheck_expr, the target propagates to:
- `typecheck_expr_cpp_name(expr, fargs, target)` — extends fargs
  with target-type info;
- `typecheck_expr_initializer_list(expr, target)` — matches
  against the target ([over.ics.list], [dcl.init.list]);
- `typecheck_expr_address_of(expr, target)` — applies
  [temp.deduct.funcaddr] when the target is a pointer-to-code;
- `typecheck_side_effect_function_call(expr, target)` — applies
  [temp.deduct.conv] when the target is a destination type for
  a returned conversion-function-template.

**Pros:** explicit, localised, matches the standard's "target type
of a context" wording.
**Cons:** touches every `typecheck_expr` caller — dozens of sites
across `src/cpp/`.  Each needs a decision: what target, if any,
to thread.

### 2.2 Option B — thread-local target-type stack on `cpp_typecheckt`

```cpp
class cpp_typecheckt {
  …
  std::vector<typet> target_type_stack;

  struct target_type_guardt {
    cpp_typecheckt &t;
    explicit target_type_guardt(cpp_typecheckt &_t, const typet &target)
      : t(_t) { t.target_type_stack.push_back(target); }
    ~target_type_guardt() { t.target_type_stack.pop_back(); }
  };
};
```

Callers that want to establish a target:
```cpp
{
  target_type_guardt g{*this, parameter.type()};
  typecheck_expr(arg);
}
```

Inside the resolver, `target_type_stack.empty() ? nullptr :
&target_type_stack.back()` is the current target.

**Pros:** no API change to `typecheck_expr`; a single RAII type.
**Cons:** hidden dependency — reviewers can't tell by reading a
call site what target context is in effect; interacts badly with
recursion through subexpressions that don't belong to the target.

### 2.3 Chosen approach — Option A with a helper type

Thread via an explicit parameter, but introduce a tiny wrapper to
keep call-site ergonomics reasonable:

```cpp
/// Target-type context per [over.ics.general]/5, [dcl.init]/16-17,
/// [temp.deduct.funcaddr]/1, [temp.deduct.conv]/1.
class target_typet
{
public:
  target_typet() = default;  // no target
  explicit target_typet(const typet &t) : target(&t) {}
  const typet *get() const { return target; }
  explicit operator bool() const { return target != nullptr; }
private:
  const typet *target = nullptr;  // non-owning; caller must keep alive
};

void typecheck_expr(exprt &expr, const target_typet &target = {});
```

Non-owning pointer semantics because the target is always a
`parameter.type()` or `symbol.type` that the caller already owns.
No target is the zero-args default.

This is Option A's discipline (explicit parameter everywhere) with
Option B's no-change-for-most-callers ergonomics (default argument).

## 3. Phased migration

### Phase 1 — introduce the API without behaviour change (2 days)

- Commit A: add `target_typet`.  Add default argument to
  `typecheck_expr` and forward to the existing implementation.  No
  behaviour change: no call site passes a target.
- Commit B: propagate `target_typet` through the internal dispatch
  in `typecheck_expr`, `typecheck_expr_main`, and the per-kind
  handlers (`typecheck_expr_cpp_name`, `typecheck_expr_address_of`,
  `typecheck_side_effect_function_call`, `typecheck_expr_initializer_list`).
  Still no call site passes a target; the extra parameter sits
  unused.
- Commit C: add `target_typet` to the `fargs` struct as an optional
  field so the resolver can see the outer call's target without
  changing every `resolve` signature.

Regression gates: bit-identical behaviour at every commit.  MSVC
26/26.  Dog-food unchanged.

### Phase 2 — [temp.deduct.funcaddr] (1 day)

- Commit D: in `typecheck_side_effect_function_call`, after the
  function is tentatively resolved (probe from the existing helper),
  pass the target parameter type to each argument's typecheck via
  `target_typet`.  Keep the probe-retry helper alongside for now —
  it becomes dead code but the removal is a separate commit.
- Commit E: in `typecheck_expr_cpp_name`, when the target is a
  pointer-to-code, synthesise fargs from the target's parameter
  types (same synthesis as today's
  `deduce_function_address_args_from_target`, just driven forward
  instead of backward).
- Commit F: in `typecheck_expr_address_of`, same — when the
  operand is an unresolved cpp_name naming a function template and
  the target is a pointer-to-code, drive deduction.

Regression gates: `cpp11_deduct_funcaddr` still passes as CORE.
Dog-food unchanged (same outcomes, different path).

### Phase 3 — retire the probe-retry helper (1 day)

- Commit G: delete `deduce_function_address_args_from_target` and
  its call site.  Retain the docstring as a comment on the forward
  path so future readers understand the history.
- Commit H: delete the fargs probe block in
  `typecheck_side_effect_function_call`.

Regression gates: still all green.

### Phase 4 — [temp.deduct.conv] (2 days)

- Commit I: in `cpp_typecheck_conversions.cpp`, when a
  user-defined conversion-function-template is a candidate for an
  implicit conversion to a specific target type, pass the target as
  P per [temp.deduct.conv]/1.  Today this deduction is attempted
  only via the already-typechecked operand path; many conversion
  cases can succeed once the target drives deduction directly.

Regression gates: new targeted test in
`regression/cbmc-cpp/cpp11_deduct_conv/` for a conversion-template
with a non-trivial target.  Dog-food should show improvement on
files that use implicit user-defined conversions to target types
(expect single-digit OK_CLEAN increase).

### Phase 5 — [over.ics.list] / [dcl.init.list] (3 days)

- Commit J: in `typecheck_expr_initializer_list`, when the target is
  a class type with a constructor accepting `std::initializer_list<T>`,
  match the brace-init-list against `initializer_list<T>` directly
  per [over.ics.list.ilist].  Retire the after-the-fact
  `implicit_typecast` path for this case.
- Commit K: extend to aggregate initialization per [dcl.init.aggr].

Regression gates: `cpp17_tuple_basic`, `cpp17_apply_basic`,
brace-init tests should stay green.  Dog-food should close the 35
`char [N]` → `basic_string` family (a specific instance of
`basic_string(initializer_list<char>)` — no, actually this is
`basic_string(const char*)` driven by target, so it lives partly
in Phase 4).

### Phase 6 — audit and cleanup (1 day)

- Commit L: audit all `typecheck_expr` call sites in `src/cpp/`
  and update the ones that have a natural target to pass it.
- Commit M: remove the now-dead code from
  `typecheck_function_call_arguments`'s post-hoc conversion path
  where the target-driven Phase 4/5 work subsumed it.

## 4. Call-site audit (Phase 6 preview)

`typecheck_expr` is called from ~80 sites.  Classified by whether a
target type is naturally available:

| count | context | has natural target? |
|-------|---------|---------------------|
|  ~25  | sub-expression of an operator (arithmetic, comparison, logical) | no — operator semantics drive the target, not the other way |
|  ~15  | argument of a function call | yes — parameter type |
|   ~8  | initializer for a variable declaration | yes — variable type |
|   ~6  | return-statement operand | yes — function return type |
|   ~4  | throw-expression operand | yes — (advisory) exception type |
|   ~4  | assignment RHS | yes — LHS type |
|   ~3  | subscript expression | partial — array element type |
|  ~15  | other (decltype, sizeof, etc.) | no |

The ~40 "yes" sites are where the Phase 6 audit adds target-typet
arguments.  The rest stay at default.

## 5. Testing strategy

### Regression gates (every commit)

- `ctest -L CORE` all-platforms-clean.
- `cpp11_deduct_funcaddr` CORE (from my `d612fe6dac` promotion).
- MSVC preprocessed headers 26/26.
- Dog-food `--expand` — record delta.

### New tests

- `regression/cbmc-cpp/cpp11_deduct_conv/` — conversion-function
  template with a target-driven deduction.  CORE.
- `regression/cbmc-cpp/cpp11_init_list_target/` — brace-init-list
  binding to `initializer_list<T>` via target.  CORE.
- `regression/cbmc-cpp/cpp11_aggregate_init_target/` — aggregate
  initialization via brace-init-list with target driving the
  match.  CORE.

## 6. Risks

| risk | probability | severity | mitigation |
|------|-------------|----------|------------|
| A target threaded to a sub-expression produces a wrong-typed result | low | medium | Phase 1 only threads the parameter without using it.  Phase 2–5 add use cases one at a time with regression gates. |
| The probe-retry helper is removed before its replacement covers every case | low | high | Phase 3 is a dedicated commit after Phase 2 lands.  If any test regresses, revert-at-commit-granularity. |
| Target-driven brace-init-list changes break a currently-working implicit conversion | medium | medium | Phase 5 lands after Phase 4; if an existing initializer regresses, the commit is small and revertible. |
| [temp.deduct.conv] is subtler than my summary suggests | medium | low | Start with the simplest case (single user-defined conversion-template, target is a concrete type) and expand in subsequent commits. |

## 7. Success criteria

1. `deduce_function_address_args_from_target` probe-retry helper is
   deleted.
2. `cpp11_deduct_funcaddr` still passes as CORE.
3. New CORE tests `cpp11_deduct_conv`, `cpp11_init_list_target`,
   `cpp11_aggregate_init_target` all green.
4. Dog-food `--expand` shows the char-array-to-basic_string class of
   failures retired (from ~35 to 0 or single digits).
5. MSVC preprocessed headers remain 26/26.
6. `typecheck_side_effect_function_call` is under 500 non-comment
   lines (retires the `check-cpplint` `readability/fn_size` finding
   from the 2026-05-13 push).

## 8. Dependencies and ordering

- Depends on: `sfinae_contextt` (landed).
- Independent of: lazy class-body elaboration.  Can go in parallel
  if staff is available.  If sequential, this plan first (smaller,
  mechanical, retires one complete cluster of dog-food failures),
  then lazy elaboration.
- Blocks: retirement of `deduce_function_address_args_from_target`
  (Phase 3 of this plan does it).
