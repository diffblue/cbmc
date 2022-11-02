# History Variables {#contracts-history-variables}

Back to @ref contracts-user

@tableofcontents

## In Function Contracts

### Syntax

```c
__CPROVER_old(*identifier*)
```

Refers to the value of a given object in the pre-state of a function within the
_ensures_ clause.

**Important.** This function may be used only within the context of `__CPROVER_ensures`.

### Parameters

`__CPROVER_old` takes a single argument, which is the identifier
corresponding to a parameter of the function. For now, only scalars,
pointers, and struct members are supported.

### Semantics

To illustrate the behavior of `__CPROVER_old`, take a look at the example
bellow.  If the function returns a failure code, the value of `*out` should not
have been modified.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Postconditions */
__CPROVER_ensures((__CPROVER_return_value == FAILURE) ==> (*out == __CPROVER_old(*out)))
/* Writable Set */
__CPROVER_assigns(*out)
{
  /* ... */
}
```

## In Loop Contracts

TODO: Document `__CPROVER_loop_entry` and `__CPROVER_loop_old`.

## Additional Resources

- @ref contracts-functions
  - @ref contracts-requires-ensures
  - @ref contracts-assigns
  - @ref contracts-frees
- @ref contracts-loops
  - @ref contracts-loop-invariants
  - @ref contracts-decreases
  - @ref contracts-assigns
  - @ref contracts-frees
- @ref contracts-memory-predicates
- @ref contracts-history-variables
- @ref contracts-quantifiers
