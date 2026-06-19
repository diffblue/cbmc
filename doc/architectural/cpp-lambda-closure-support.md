# C++ Lambda / Closure Support Rework

Status: implemented.  Phases A (captureless closure class), B (by-copy
captures), C (by-reference captures), D (mutable), E (capture-defaults and
this/*this capture), and F (generic lambdas as member function templates) are
all implemented.  Remaining function-pointer-lowering fallbacks (sound for their
cases) are noted per phase below.

Companion tests: `regression/cbmc-cpp/cpp11_lambda_closure_in_std_function`
(CORE), `cpp11_lambda_captureless_closure` (CORE), and the capturing-lambda
soundness KNOWNBUGs (`cpp11_lambda_capture_by_value_snapshot`,
`cpp11_lambda_capture_per_instance`, `cpp11_lambda_mutable_state`).

## 1. Motivation

CBMC's C++ front end lowers a lambda expression to an ordinary **function**
plus a **function pointer**: the lambda body becomes a file-local function
`__lambda_N`, captured entities become file-local symbols, and the lambda
expression is replaced by `&__lambda_N`.  This is not a closure *object*, so it
diverges from the standard model in ways that are both *incomplete* (a lambda
cannot be stored by value, e.g. in `std::function`) and *unsound* (captures do
not behave as copies / per-object state).

## 2. Empirical baseline (current behaviour)

Header-free probes, each a single `__CPROVER_assert` checked to be present in
`--show-properties` (i.e. non-vacuous).  "OK" = assertion proven; "WRONG" =
assertion fails although it should hold.

| Probe | Construct | Result |
|---|---|---|
| captureless call | `auto f=[](int x){return x+1;}; f(4)` | OK |
| by-value, var unchanged | `int a=10; [a](int x){return x+a;}(5)` | OK |
| by-reference | `int a=10; auto f=[&a]{...}; a=20; f()` sees 20 | OK |
| **by-value snapshot** | `int a=10; auto f=[a]{...}; a=20; f()` should see **10** | **WRONG** (sees 20) |
| `[=]` default copy | `[=](int x){return x+a+b;}` | OK |
| `[&]` default ref | `[&](int x){a+=x; ...}` | OK |
| init-capture | `[y=42](int x){return x+y;}` | OK |
| generic | `[](auto x){return x+1;}` | OK |
| algorithm + capture | `count_if(b,e,[t](int x){return x>=t;})` | OK |
| lambda returning lambda | `[](int a){return [a](int b){return a+b;};}` | OK |
| **mutable per-call state** | `[a]() mutable {a+=1; return a;}` called twice | **WRONG** |
| **two instances, same type** | `make_adder(3)`, `make_adder(10)` independent | **WRONG** (shared) |
| **counter factory** | `[s]() mutable {return s++;}` per-instance | **WRONG** |
| std::function from lambda | `std::function<int(int)> f = []...; f(4)` | **WRONG** (null call) |

The cases marked OK happen to coincide with correct behaviour only because they
use a *single* instance whose captured variables are *not modified* between
capture and call.

### Root cause

There is no closure object.  A capture is a single, shared, `file_local
state_var` symbol (e.g. `make_adder(int)::1::__lambda_1::n`), and the lowered
function reads/initialises it *at call time* rather than copying it into a
per-object member *at capture time*.  Consequently:

  * **by-value capture is effectively by-reference** — it observes the live
    variable at call time, not a copy taken at capture time
    (violates [expr.prim.lambda.capture], see §3);
  * **all instances of one lambda type share the same capture storage** — a
    second construction overwrites the first's captures (the factory pattern);
  * **`mutable` lambdas have no persistent per-object state**;
  * **the lambda is a pointer, not an object**, so it cannot be stored by value
    (`std::function`, `std::bind`, returned/escaping closures that outlive the
    captured variable's scope, etc.).

## 3. What the standard requires (N5008, [expr.prim.lambda])

  * **[expr.prim.lambda.closure]/1** — the type of a lambda-expression (and of
    the closure object) is "a unique, unnamed non-union class type, called the
    closure type."  So a lambda is an **object of a class type**, never a
    function pointer.
  * **/2** — the closure type is declared in the smallest enclosing block,
    class, or namespace scope.
  * **/3** — the closure type is *not* an aggregate; it is a *structural type*
    iff the lambda has no capture.  An implementation "may define the closure
    type differently … provided this does not alter the observable behavior"
    other than size/alignment/triviality.  This is the licence for our
    representation freedom — but observable behaviour (capture-by-copy
    semantics, per-object state) must match.
  * **§7.5.6.2** — for a **non-generic lambda with no lambda-capture** the
    closure type has a non-explicit **conversion function to pointer to
    function** with the same parameter and return types.  (Also for generic
    captureless lambdas, per template.)
  * **[expr.prim.lambda.closure]** — the closure type has a public inline
    **function call operator** (`operator()`); it is `const`-qualified unless
    the lambda is `mutable` (or `static`, C++23).
  * **[expr.prim.lambda.capture] (≈/7)** — "For each entity captured by copy, an
    unnamed **non-static data member** is declared in the closure type"; within
    the body, each odr-use of such an entity is transformed into an access to
    the corresponding member of the closure object.  The member is
    direct-initialised from the entity **at the point the closure object is
    created** (capture time).
  * **[expr.prim.lambda.capture]** — an entity **captured by reference** is
    captured as a reference; by-reference members observe the referenced entity.
  * **init-capture** (`[y = expr]`, `[&y = expr]`) declares a member of the
    deduced type, initialised from `expr` at capture time.
  * **`*this` / `this` capture** — `[this]` captures the enclosing object by
    reference (a pointer member); `[*this]` (C++17) captures it by copy.
  * **generic lambda** ([expr.prim.lambda.closure]) — the call operator is a
    **member function template** (`auto`/template parameters); each call
    instantiates it.

## 4. Target design

Model a lambda as its **closure class** (a struct), constructed at the
lambda-expression's evaluation point and initialised from the captures.  A
struct functor already verifies end-to-end in CBMC (calls lower to
`operator()(&obj, args...)`, and `std::function`/`std::ref`/algorithms store and
invoke such objects), so the closure struct reuses that machinery.

For lambda `L` at scope `S`:

  * Synthesise `struct S::__lambdaN_closure { ... };`:
    * one **non-static data member per by-copy capture**, of the captured
      entity's (decayed) type;
    * one **reference/pointer member per by-reference capture** (and a pointer
      member for `[this]`);
    * `Ret operator()(Params) [const] { body }` — `const` unless `mutable`;
      odr-uses of captures rewritten to `this->member`;
    * for a **captureless** lambda, a non-explicit `operator Ret(*)(Params)()
      const` returning the address of a static thunk (the existing `__lambda_N`
      body), to preserve every current function-pointer use site.
  * Replace the lambda expression with a **closure object** of that type:
    * captureless → `struct_exprt{{}, closure_tag}` (a stateless value);
    * with captures → a temporary initialised with the capture values
      (by-copy: copy the entity *now*; by-reference: take its address now).
  * Calls (`f(args)`), storage (`std::function`), copies and template argument
    deduction then all work because the lambda is a normal class object.

The robust way to create the closure class is to synthesise its
`cpp_declaration` and run it through the existing class type-checker
(`convert`/`typecheck_compound_type`), rather than hand-building struct
components and method symbols.

## 5. Phased plan

Each phase: KNOWNBUG test first, flip to CORE on completion, gate **both**
`regression/cbmc-cpp` and `regression/cbmc`, keep the existing ~31 lambda tests
green.

  * **Phase A — captureless closure class.**  DONE.  Struct with `operator()`
    (body) and a non-explicit conversion to pointer-to-function (returning the
    lowered function/thunk).  The lambda expression is a materialised
    `temporary_object` of the closure type.  All current function-pointer use
    sites keep working via the conversion; std::function stores and invokes a
    captureless lambda.  Flipped `cpp11_lambda_closure_in_std_function`; added
    `cpp11_lambda_captureless_closure`.  C++23 deducing-this (explicit object
    parameter) lambdas keep the function-pointer lowering for now.
  * **Phase B — by-copy captures as members.**  DONE (explicit by-copy
    captures).  A data member per by-copy capture, named after the entity (so
    body odr-uses resolve by member lookup), direct-initialised from the entity
    at the capture point; operator() return type deduced freshly.  Fixes
    `byval_snapshot` and `factory`/per-instance (flipped
    `cpp11_lambda_capture_by_value_snapshot`,
    `cpp11_lambda_capture_per_instance` to CORE).  The closure type is memoised
    per lambda source location (auto return type deduction type-checks a lambda
    more than once).  `mutable` is now recorded by the parser.  Still on the
    function-pointer lowering: capture-defaults (`[=]`/`[&]`), by-reference
    captures, `mutable`, and lambdas whose body contains a nested lambda
    (closure-typed return).
  * **Phase C — by-reference captures.**  DONE (explicit by-reference
    captures).  A reference member per by-reference capture, bound at the
    capture point to the entity (a reference is modelled as the entity's
    address); body odr-uses resolve to it by member lookup and denote the
    entity, and a const lambda may modify the referent through it.  Added
    `cpp11_lambda_capture_by_reference` (CORE).  Still on the function-pointer
    lowering: capture-defaults (`[=]`/`[&]`), this/*this captures, `mutable`,
    and nested-lambda-returning bodies.
  * **Phase D — `mutable`.**  DONE.  A mutable lambda is lowered to a closure
    whose operator() is non-const; its by-copy capture members (Phase B) are
    therefore mutable and modifications persist in the closure object across
    calls.  Flipped `cpp11_lambda_mutable_state` to CORE; added
    `cpp11_lambda_mutable_counter_factory` (independent persistent counters).
  * **Phase E — capture-defaults; this/*this; init-capture.**  DONE.
    Capture-defaults `[=]`/`[&]` are handled by odr-use discovery (simple
    identifiers in the body resolving to automatic locals in the enclosing
    scope) and captured per the default (by copy = snapshot, by reference =
    live), with explicit captures overriding; init-capture `[y = expr]` is
    handled by Phase B.  In a member-function context, `[this]`/`[=]`/`[&]` (and
    `[*this]`, now parsed) are modelled as captures of the odr-used non-static
    data members -- by reference for `this`/`[=]`/`[&]` (live, modifiable) or by
    copy for `[*this]` (a snapshot at capture time).  Tests:
    `cpp11_lambda_capture_default`, `cpp11_lambda_capture_this` (CORE).  Still on
    the function-pointer lowering: a lambda that uses `this` explicitly or
    odr-uses a member function (member-function calls within the lambda are not
    yet modelled on the closure path).
  * **Phase F — generic lambdas as member function templates.**  DONE.  A
    closure-eligible generic lambda is lowered to its closure class with
    operator() synthesised as a member function template: each `auto` parameter
    becomes an invented template type parameter (a C++20 `[]<typename T>(...)`
    names them), operator() has a deduced (`auto`) return type unless specified,
    and calls instantiate the template as for any struct functor.  Its captures
    are real closure members (Phases B/C/D/E), so a generic by-copy capture
    snapshots at capture time and factory-produced closures have independent
    state.  Added `cpp11_lambda_generic_closure` (CORE).  Generic lambdas that
    capture by reference (a deduced return type mishandles a reference-member
    access), are in a member-function context, have an explicit object
    parameter, or whose body contains a nested lambda keep the call-site
    instantiation (`generic_lambda_map`) lowering.

## 6. Risks and integration points

  * **~31 existing lambda tests** plus the bespoke **generic-lambda
    instantiation** machinery (`generic_lambda_map`, call-site re-type-check).
    Phase F subsumes the latter; until then generic lambdas keep the current
    path.
  * **Function-pointer use sites.**  Preserved in Phase A by the
    conversion-to-function-pointer on captureless closures.  Capturing lambdas
    are not function-pointer-convertible (correct per standard), so any current
    test that passes a *capturing* lambda where a function pointer is required
    is already ill-formed and should be reviewed.
  * **Temporary/object representation and overload resolution.**  Reuse the
    struct-functor lowering (`operator()(&obj, args...)`) and the standard
    closure-object copy semantics.
  * **decltype / unevaluated lambdas, constexpr lambdas, lambdas in templates**
    — covered by treating the closure as an ordinary class type; add targeted
    tests.

## 7. Test matrix (to become regression tests)

The §2 probes become regression tests (KNOWNBUG where currently WRONG, flipped
to CORE per phase): captureless call; by-value (unchanged and *snapshot*);
by-reference; `[=]`/`[&]`; init-capture; `mutable` (per-call and counter
factory); two-instances-same-type / factory; generic; algorithm-with-capture;
lambda-returning-lambda (escaping closure); `std::function` from a lambda;
`this`/`*this` capture in a member function.
