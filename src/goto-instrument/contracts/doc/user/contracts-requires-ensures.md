# Requires and Ensures Clauses {#contracts-requires-ensures}

Back to @ref contracts-user

@tableofcontents

## Syntax

```c
__CPROVER_requires(bool cond)
```

A _requires_ clause specifies a precondition for a function, i.e., a property
that must hold to properly execute the function. Developers may see the
_requires_ clauses of a function as obligations on the caller when invoking the
function. The precondition of a function is the conjunction of the _requires_
clauses, or `true` if none are specified.

```c
__CPROVER_ensures(bool cond)
```

An _ensures_ clause specifies a postcondition for a function, i.e., a property
over arguments or global variables that the function guarantees at the end of
the operation. Developers may see the _ensures_ clauses of a function as the
obligations of that function to the caller. The postcondition of a function is
the conjunction of the _ensures_ clauses, or `true` if none are specified.

Both _requires_ clauses and _ensures_ clauses take a Boolean expression over the
arguments of a function and/or global variables. The expression can include
calls to CBMC built-in functions or to
[Memory Predicates](@ref contracts-memory-predicates)).
User-defined functions can also be called inside _requires_ clauses as long as
they are deterministic and do not have any side-effects
(the absence of side effects is checked by the tool). In addition, _ensures_
clauses also accept [History Variables](@ref contracts-history-variables)
and the special built-in symbol `__CPROVER_return_value` which represents the
return value of the function.

## Semantics

The semantics of _ensures_ and _requires_ clauses can be understood in two
contexts: enforcement and replacement.  To illustrate these two perspectives,
consider the following implementation of the `sum` function.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
__CPROVER_ensures(
  __CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures(
  (__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
__CPROVER_assigns(*out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}
```

### Enforcement

In order to determine whether _requires_ and _ensures_ clauses are a sound
abstraction of the behavior of a function *f*, CBMC will try to check them
as follows:

1. Considers all arguments and global variables as non-deterministic values;
2. Assumes all preconditions specified in the `__CPROVER_requires` clauses;
4. Calls the implementation of function *f*;
5. Asserts all postconditions described in the `__CPROVER_ensures` clauses.

In our example, the `sum` function will be instrumented as follows:

```c
// The original sum function with a mangled name
int __CPROVER_contracts_original_sum(
  const uint32_t a, const uint32_t b, uint32_t* out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}

/* Function contract enforcement wrapper */
int sum(uint32_t a, uint32_t b, uint32_t* out)
{
  // assume the requires clause
  __CPROVER_assume(__CPROVER_is_fresh(out, sizeof(*out)));

  // declare local to represetn __CPROVER_return_value
  int __return_value;

  // call function under verification
  __return_value = __CPROVER_contracts_original_sum(a, b, out);

  // check the first ensures clause
  __CPROVER_assert(
    __return_value == SUCCESS || __return_value == FAILURE,
    "Check ensures clause");

  // check the second requires clause
  __CPROVER_assert(
    (__return_value == SUCCESS) ==> (*out == (a + b)),
    "Check ensures clause");

  return __return_value;
}
```

### Replacement

Assuming _requires_ and _ensures_ clauses are a sound abstraction of the
behavior of the function *f*, CBMC will use the function contract in place of
the function implementation as follows:

1. Adds assertions for all preconditions specified in the `__CPROVER_requires`
  clauses;
2. Adds non-deterministic assignments for each symbol listed in the
   `__CPROVER_assigns` clause (see [Assigns Clauses](@ref contracts-assigns)
  for details);
2. Adds non-deterministic free statements for each symbol listed in the
   `__CPROVER_frees` clause (see [Frees Clauses](@ref contracts-frees)
  for details);
3. Assumes all postconditions described in the `__CPROVER_ensures` clauses;

In our example, consider that a function `foo` may call `sum`.

```c
int foo()
{
  uint32_t a = ... ;
  uint32_t b = ... ;
  uint32_t out = 0;
  int rval = sum(a, b, &out);
  if (SUCCESS != rval)
    return FAILURE;

  // else, use out
  utin32_t result = out + ...;
}
```

CBMC will use the function contract in place of the function implementation
wherever the function is called.

```c
int foo()
{
  uint32_t a = ...;
  uint32_t b = ...;
  uint32_t out = 0;

  // start of call-by-contract replacement
  // check if preconditions hold
  __CPROVER_assert(
    __CPROVER_is_fresh(out, sizeof(*out)), "Check requires clause");

  // nondet return value
  int __return_value = nondet_int();

  // assume postconditions
  __CPROVER_assume(__return_value == SUCCESS || __return_value == FAILURE);
  __CPROVER_assume((__return_value == SUCCESS) ==> (*out == (*a + *b)));

  int rval = __return_value;
  // end of call-by-contract replacement

  if (SUCCESS != rval)
    return FAILURE;

  // else, use out
  utin32_t result = out + ...;
}
```

## Additional Resources

- @ref contracts-functions
  - @ref contracts-requires-ensures
  - @ref contracts-requires-ensures-contract
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
