# Function Contracts Reminder {#contracts-dev-spec-reminder}

Back to top @ref contracts-dev-spec

@tableofcontents

The user documentation for function contracts is available at @ref contracts-functions,
but we briefly remind the developer of the structure of a contract below.


A contract is defined by adding one or more clauses to a function declaration or
definition:

```c
ret_t foo(parameters)
// preconditions
__CPROVER_requires(R)

// postconditions
__CPROVER_ensures(E)

// frame conditions
__CPROVER_assigns(A)
__CPROVER_frees(F)
;
```

- A `__CPROVER_requires` clause (@ref contracts-requires-ensures) specifies a
  precondition as boolean expression R that may only depend on program globals,
  function parameters, [memory predicates](@ref contracts-memory-predicates),
  [function pointer predicates](@ref contracts-function-pointer-predicates) and
  deterministic, side effect-free function calls;
- A `__CPROVER_ensures` clause (@ref contracts-requires-ensures) specifies a
  postcondition as boolean expression E that may only depend on program globals,
  function parameters, [memory predicates](@ref contracts-memory-predicates),
  [function pointer predicates](@ref contracts-function-pointer-predicates),
  deterministic, side effect-free function calls,
  [history variables](@ref contracts-history-variables), and the special
  variable `__CPROVER_return_value`;
- A `__CPROVER_assigns` clause (@ref contracts-assigns) specifies a set A of
  memory locations that may be assigned to by any function satisfying the
  contract;
- A `__CPROVER_frees` clause (@ref contracts-frees) specifies a set F of
  pointers that may be freed by any function satisfying the contract.

For each such function `foo` carrying contract clauses, the ansi-c front-end of
CBMC creates a dedicated function symbol named `contract::foo` in the symbol table,
with the same signature as `foo`, and attaches the contract clauses to that new
symbol. We call `contract::foo` the **pure contract** associated with the function
`foo`.

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec | @ref contracts-dev-spec-transform-params