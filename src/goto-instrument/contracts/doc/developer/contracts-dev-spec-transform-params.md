# Program Transformation Overview {#contracts-dev-spec-transform-params}

Back to top @ref contracts-dev-spec

@tableofcontents

These are the main parameter of the program transformation:

- `harness_id` specifies the identifier of the proof harness;
- `(f_top,c_top)` an optional pair and specifies that
  the function `f_top` must be checked against the contract carried by function
  `c_top`, by the pure contract `contract::c_top`.
- `(f,c)` a possibly empty set of pairs where each `f` must be replaced
  with the contract carried by function `c`, i.e. by the pure contract `contract::c`.

The program transformation steps are applied as follows:
1. @ref contracts-dev-spec-codegen is applied to all contracts to check or replace;
2. @ref contracts-dev-spec-dfcc is applied to all library or user-defined goto functions;
3. @ref contracts-dev-spec-harness is applied to the harness function;
4. @ref contracts-dev-spec-contract-checking is applied to the function to be checked against a contract;
5. @ref contracts-dev-spec-contract-replacement is applied to each function to be replaced by a contract;

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-reminder | @ref contracts-dev-spec-codegen
