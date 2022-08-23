# Dynamic Frame Condition Checking {#contracts-dev-spec-dfcc}

Back to top @ref contracts-dev-spec

@tableofcontents

## Overview
Frame condition checking consists in checking that a function (and any
functions it calls) only assigns to memory locations allowed by the contract's
assigns clause, and only deallocates objects allowed by the contract's frees
clause.

To implement frame condition checking we use a method inspired by
[Dynamic Frames](https://pm.inf.ethz.ch/publications/Kassios11.pdf).

The method consists in:
- representing sets of assignable and freeable memory locations specified by
  contracts as ghost data structures embedded in the program under verification;
- extending all functions of the model to accept an additional dynamic frame
  parameter;
- instrumenting all functions to check that the side effects or the deallocation
  they perform are within what is allowed by the dynamic frame parameter.

In our approach a dynamic frame is represented by the
@ref __CPROVER_contracts_write_set_t data type defined in @ref cprover_contracts.c.

From an simple point of view, a @ref __CPROVER_contracts_write_set_t
tracks 4 sets of memory locations:

```c
struct __CPROVER_contracts_write_set_t {

  // from the contract's __CPROVER_assigns clause
  __CPROVER_contracts_car_set_t contract_assign;

  // from the contract's __CPROVER_frees clause
  __CPROVER_contracts_obj_set_t contract_frees;

  // records local allocations
  __CPROVER_contracts_obj_set_t allocated;

  // records deallocations
  __CPROVER_contracts_obj_set_t deallocated;

} __CPROVER_contracts_write_set_t;
```

- `contract_assigns` is the set of memory locations specified in the
  *assigns clause* of the contract of interest;
- `contract_frees` is the set of pointers specified in the *frees clause*
  of the contract of interest;
- `allocated` is the set of identifiers of objects
  (as given by `__CPROVER_POINTER_OBJECT(x)`) that were locally allocated
  since first entering the function under verification
  (on the stack using `DECL x` or on the heap using
  `x = __CPROVER_allocate(...)`);
- `deallocated` is the set of pointers `p` that were deallocated using
  `__CPROVER_deallocate(p)` since first entering the function under
  verification.

The @ref __CPROVER_contracts_write_set_t type is accompanied by functions
allowing to (cf @ref cprover_contracts.c):
- add contents to `contract_assigns`;
- add contents to `contract_frees`;
- record an object allocation in `allocated`;
- record an object deallocation in `deallocated`;
- check wether a given `car_t` describing a location about to be assigned is
  contained within `contract_assigns` or `allocated`;
- check wether the object pointed to by a given pointer about to be freed is
  contained in `contract_frees` or `allocated`;
- check weither all memory locations of a candidate write set are included in
  some element of a given reference write set.

The instrumentation adds a @ref __CPROVER_contracts_write_set_ptr_t parameter
to all functions of the GOTO model as follows:

```c
ret_t f(<original-parameters>, __CPROVER_contracts_write_set_ptr_t write_set);
```

The bodies of the functions are instrumented so that:
- when the given `write_set` is `NULL`, no checks are performed;
- when the given `write_set` is not `NULL`, the following checks are performed:
  - The address ranges corresponding to the LHS of assignments instructions are
    checked for inclusion in `contract_assigns` or `allocated`;
  - stack-allocated objects (`DECL`) and heap-allocated objects
    (`__CPROVER_allocate`) are recorded in `allocated`
  - dynamic objects deallocated with `__CPROVER_deallocate` are checked for
    inclusion in `contract_frees` or `allocated`, and are recorded in
    `deallocated` (so that contract postconditions about deallocations
    can be checked).
  - the `write_set` parameter is propagated to functions calls or
    function pointer calls.

## Detailed Specifications

- @subpage contracts-dev-spec-dfcc-runtime Gives details on the write set implementation
- @subpage contracts-dev-spec-dfcc-instrument Gives function instrumentation rules

---
 Prev | Next
:-----|:------
 @ref contracts-dev | @ref contracts-dev-spec-dfcc-runtime