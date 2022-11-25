# Rewriting Calls to the __CPROVER_obeys_contract Predicate {#contracts-dev-spec-obeys-contract}

Back to top @ref contracts-dev-spec

@tableofcontents


The `__CPROVER_obeys_pointer` is defined as follows:
if the predicate holds then `function_pointer` points to a
function satisfying the `contract` passed as second argument.
If the predicate does not hold, then nothing can be assumed of the
`function_pointer` behaviour.


The instrumentation of `__CPROVER_obeys_contract` is supported by the
class @ref dfcc_obeys_contractt. In a GOTO program passed as argument,
this class rewrites calls to:

```c
CALL retval := __CPROVER_obeys_contract(function_pointer, contract);
```

into calls to the library function implementation:

```c
CALL retval := __CPROVER_contracts_obeys_contract(
    &function_pointer,
    contract,
    write_set);
```

One thing to notice is that the library implementation function takes the
`function_pointer` argument by reference:

```c
__CPROVER_contracts_obeys_contract(
    void (**function_pointer)(void),
    void (*contract)(void),
    __CPROVER_contracts_write_set_ptr_t write_set);
```

This function implements the `__CPROVER_obeys_contract` behaviour for all
different contexts (contract checking vs replacement, requires vs ensures clause
context, as described by the flags carried by the write set parameter).

In an assumption context, the predicate turns into a nondet assignment that
makes `function_pointer` point to the `contract` function:

```c
if(nondet_bool()) {
    *function_pointer = contract;
    return true;
} else {
    return false;
}
```

If the surrounding `__CPROVER_assume` statement enforces a true value for the
predicate, then the `function_pointer` will effectively point to the `contract`
function, which is known to satisfy its own specification.

If the surrounding `__CPROVER_assume` statement enforces a false value for the
predicate, then nothing is enforced on the `function_pointer`
(it could be invalid, be NULL, point to any other function, etc.).

In assertion contexts, the predicate turns into a pointer equality check:

```c
  return *function_pointer == contract;
```


In addition to rewriting calls, the `dfcc_obeys_contractt` class reports all
contract functions discovered as second arguments of the predicates.
This information is then used in method
@ref dfcct#wrap_discovered_function_pointer_contracts to replace all discovered
contract functions by their actual contracts. That way, any call to a function
pointer assumed or succesfully asserted to satisfy the contract will actually
behave like the contract.

---
 Prev | Next
:-----|:------
 @ref contracts-dev | @ref contracts-dev-spec-reminder