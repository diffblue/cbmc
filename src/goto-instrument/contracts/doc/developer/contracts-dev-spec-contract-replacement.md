# Replacing a Function by a Contract {#contracts-dev-spec-contract-replacement}

Back to top @ref contracts-dev-spec

@tableofcontents

Let us now consider a function `bar`, called directly or indirectly from `main`.

Assuming that `bar` satisfies a contract `d`, we want to replace `bar` with an
abstraction derived from `d`. Checking that `bar` actually satisfies `d` is the
responsibility of the user, and will usually be done using another proof harness.

```c
int d(int *a)
__CPROVER_requires(R)
__CPROVER_ensures(E)
__CPROVER_assigns({a1, a2, ...})
__CPROVER_frees({f1, f2, ...})
;

int bar(int *a)
{
  // does something with a
}
```

We abstract `bar` by replacing its instructions with instructions modelling
the non-deterministic behavior of the contract `d`, following this template:

```c
ret_t foo(foo_params, write_set_t caller_write_set) {

  // create empty write set to check side effects in requires clauses
  __CPROVER_contracts_write_set_t __requires_write_set;
  __CPROVER_contracts_write_set_ptr_t requires_write_set;
  __CPROVER_contracts_write_set_create(requires_write_set, 0, 0);

  // assert requires clauses
  assert(contract::requires(foo_params, requires_write_set));
  assert(contract::requires_contract(foo_params, requires_write_set));

  // snapshot history variables
  hist1_t hist1 = ...;
  hist2_t hist2 = ...;

  // create contract write set
  __CPROVER_contracts_write_set_t __contract_write_set;
  __CPROVER_contracts_write_set_ptr_t contract_write_set = &__contract_write_set;
  __CPROVER_contracts_write_set_create(contract_write_set, assigns_clause_size(contract), frees_clause_size(contract));

  // populate the write set
  contract::assigns(contract_write_set, empty_write_set);
  contract::frees(contract_write_set, empty_write_set);
  assert(__CPROVER_contracts_write_set_check_allocated_deallocated_is_empty(requires_write_set));

  __CPROVER_contracts_write_set_release(requires_write_set);

  // check inclusion with caller write set
  assert(__CPROVER_contracts_write_set_check_assigns_clause_inclusion(caller_write_set, contract_write_set));

  assert(__CPROVER_contracts_write_set_check_frees_clause_inclusion(caller_write_set, contract_write_set));

  // havoc assigns clause targets
  contract::havoc(contract_write_set);
  ret_t retval = nondet();

  // free freeable pointers
  __CPROVER_contracts_write_set_deallocate_freeable(contract_write_set);

  // Create empty write set to check side effects in ensures clauses
  __CPROVER_contracts_write_set_t __ensures_write_set;
  __CPROVER_contracts_write_set_ptr_t ensures_write_set;
  __CPROVER_contracts_write_set_create(ensures_write_set, 0, 0);

  // Link caller write set and write set so that allocations due to is_fresh
  // in post conditions are recorded in the caller write set
  __CPROVER_contracts_write_set_link_allocated(ensures_write_set, caller_write_set);

  // link the ensures write set to the contract write set so that the was_freed
  // predicates in the postconditions get access to the deallocated pointers
  __CPROVER_contracts_write_set_link_deallocated(ensures_write_set, contract_write_set);

  // assume post conditions
  assume(contract::ensures(foo_params, ensures_write_set));
  assume(contract::ensures_contract(foo_params, ensures_write_set));

  // postamble
  assert(__CPROVER_contracts_write_set_check_allocated_deallocated_is_empty(ensures_write_set));
  __CPROVER_contracts_write_set_release(ensures_write_set);

  return retval;
}
```

After applying this transformation, any function that called the initial `bar`
now calls the abstraction derived from the contract.

---
 Prev | Next
:-----|:------
 @ref contracts-dev | @ref contracts-dev-spec-reminder