# C++20 Concepts Support Plan

## Current State (as of this PR)

CBMC has partial C++20 concepts support:
- **requires clauses**: Parsed and skipped (constraints treated as always satisfied)
- **Named concepts**: `template<class T> concept X = expr;` parsed as constexpr bool
- **Constrained template parameters**: `template<Concept T>` works
- **requires expressions**: `requires(T a) { a + b; }` parsed and skipped
- **Constraint counting**: Number of && conjuncts stored for specialization ordering
- **requires keyword in MSVC mode**: Enabled for VISUAL_STUDIO flavour in C++17

## Phase 1: Constraint Evaluation

### Phase 1.1: Parse requires clauses as expressions
Currently the parser skips requires clauses with a hand-written token
consumer. Replace this with proper expression parsing so constraints
can be stored and evaluated.

**Challenge**: The expression parser (`rExpression`) is greedy and may
consume tokens beyond the constraint (e.g., the return type of a
function). The requires clause grammar needs a custom expression parser
that stops at declaration keywords.

**Files**: `src/cpp/parse.cpp` (lines 1401-1497, 3871-3930, 4645-4700)
**Tests**: `regression/cbmc-cpp/cpp20_concepts_requires_expr/`
**Effort**: ~200 lines

### Phase 1.2: Evaluate type constraints
Evaluate `requires { typename T::type; }` during template instantiation
to check if a type member exists. This is the most common pattern in
STL headers (SFINAE-like behavior).

**Approach**: During partial specialization matching, when a requires
clause contains `requires { typename ... }`, attempt to resolve the
type. If resolution fails, reject the specialization.

**Files**: `src/cpp/cpp_typecheck_resolve.cpp`, `src/cpp/cpp_instantiate_template.cpp`
**Tests**: `regression/cbmc-cpp/cpp20_concepts_requires_type/`
**Effort**: ~300 lines

### Phase 1.3: Constraint-based specialization ordering
When multiple constrained partial specializations match, select the
most constrained one. Currently uses a heuristic (count && conjuncts).

**Blocker**: Specializations that differ ONLY in their requires clause
produce identical mangled names and overwrite each other. Fix requires
including constraint information in the mangled name.

**Files**: `src/cpp/cpp_type2name.cpp`, `src/cpp/cpp_typecheck_resolve.cpp`
**Tests**: `regression/cbmc-cpp/cpp20_concepts_ordering/`
**Effort**: ~300 lines

## Phase 2: Named Concepts

### Phase 2.1: Concept declarations
Already partially implemented — `concept X = expr` is parsed as
constexpr bool. Need to evaluate the expression during constraint
checking.

**Tests**: `regression/cbmc-cpp/cpp20_concepts_named/`
**Effort**: ~100 lines

### Phase 2.2: Constrained auto parameters
`void f(Concept auto x)` — abbreviated function templates.
Already works syntactically (constraint is skipped).

**Tests**: `regression/cbmc-cpp/cpp20_concepts_constrained_param/`
**Effort**: ~100 lines

## Phase 3: Advanced Features

### Phase 3.1: Constraint subsumption
Determine which constraint is "more constrained" for overload
resolution. Requires normalizing constraints to conjunctive/
disjunctive normal form and checking logical implication.

**Tests**: `regression/cbmc-cpp/cpp20_concepts_subsumption/`
**Effort**: ~500 lines

### Phase 3.2: Compound requirements
`requires(T x) { { x.size() } -> same_as<int>; }` — check that
an expression is valid AND its return type satisfies a concept.

**Tests**: `regression/cbmc-cpp/cpp20_concepts_compound_req/`
**Effort**: ~200 lines

### Phase 3.3: Nested requirements
`requires { requires sizeof(T) > 4; }` — nested requires within
a requires expression body.

**Tests**: `regression/cbmc-cpp/cpp20_concepts_nested_req/`
**Effort**: ~100 lines
