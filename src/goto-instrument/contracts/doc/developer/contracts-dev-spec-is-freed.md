# Rewriting Calls to __CPROVER_is_freeable and __CPROVER_was_freed Predicates {#contracts-dev-spec-is-freeable}

Back to top @ref contracts-dev-spec

@tableofcontents

In goto programs encoding pre or post conditions (generated from the contract clauses) and in all user-defined functions, we simply replace calls to `__CPROVER_is_freeable` with a calls to its library implementation:

```c
CALL __CPROVER_contracts_is_freeable(void *ptr, __CPROVER_contracts_write_set_ptr_t write_set);
```

The behaviour of `__CPROVER_contracts_is_freeable` can only be used in requires clauses, and it needs to use a weaker definition when used in assumption contexts (contract checking vs replacement). Context flags are obtained from the write set instance an interpreted by the library function.

For `__CPROVER_was_freed`, which can only be used in post conditions, we also map calls to a library implementation:

```c
CALL __CPROVER_contracts_was_freed(void *ptr, __CPROVER_contracts_write_set_ptr_t write_set);
```

This function performs a lookup in the `write_set->deallocated` pointer set to check if the function under analysis indeed deallocated the object. The result of this check will then be either asserted for contract checking or assumed for contract replacement. on the context. When turned in an assumption, we instantiate an extra assertion before the assumption, in order to check that the pointer is in always found in the freeable set of the contract and that it is safe to assume it is freed, without causing an immediate contradiction.

---
 Prev | Next
:-----|:------
 @ref contracts-dev | @ref contracts-dev-spec-reminder