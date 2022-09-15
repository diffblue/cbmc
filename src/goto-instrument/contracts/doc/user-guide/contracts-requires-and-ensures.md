[CPROVER Manual TOC](../../)

# Requires \& Ensures Clauses


### Syntax

```c
__CPROVER_requires(bool cond)
```

A _requires_ clause specifies a precondition for a function, i.e., a property that must hold to properly execute the operation. Developers may see the _requires_ clauses of a function as obligations on the caller when invoking the function. The precondition of a function is the conjunction of the _requires_ clauses, or `true` if none are specified.

```c
__CPROVER_ensures(bool cond)
```

An _ensures_ clause specifies a postcondition for a function, i.e., a property over arguments or global variables that the function guarantees at the end of the operation. Developers may see the _ensures_ clauses of a function as the obligations of that function to the caller. The postcondition of a function is the conjunction of the _ensures_ clauses, or `true` if none are specified.


### Parameters

A _requires_ clause takes a Boolean expression over the arguments of
a function and/or global variables, including CBMC primitive functions (e.g.,
[Memory Predicates](../../contracts/memory-predicates/)). Similarly, _ensures_ clauses also accept Boolean
expressions and CBMC primitives, but also [History Variables](../../contracts/history-variables/) and `__CPROVER_return_value`.

**Important.** Developers may call functions inside _requires_ and _ensures_
clauses to better write larger specifications (e.g., predicates). However, at
this point CBMC does not enforce such functions to be without side effects
(i.e., do not modify any global state). This will be checked in future
versions.


### Semantics

The semantics of _ensures_ and _requires_ clauses can be understood in two
contexts: enforcement and replacement.  To illustrate these two perspectives,
consider the following implementation of the `sum` function.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Precondition */
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
/* Postconditions */
__CPROVER_ensures(__CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures((__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}
```

#### Enforcement

In order to determine whether _requires_ and _ensures_ clauses are a sound
abstraction of the behavior of a function *f*, CBMC will try to check them
as follows:

1. Considers all arguments and global variables as non-deterministic values;
2. Assumes all preconditions specified in the `__CPROVER_requires` clauses;
4. Calls the implementation of function *f*;
5. Asserts all postconditions described in the `__CPROVER_ensures` clauses.

In our example, the `sum` function will be instrumented as follows:

```c
/* Function Contract Enforcement */
int sum(uint32_t a, uint32_t b, uint32_t* out)
{
  __CPROVER_assume(__CPROVER_is_fresh(out, sizeof(*out)));
  
  int return_value_sum = __CPROVER_contracts_original_sum(a, b, out);
  
  __CPROVER_assert(return_value_sum == SUCCESS || return_value_sum == FAILURE, "Check ensures clause");
  __CPROVER_assert((return_value_sum == SUCCESS) ==> (*out == (a + b)), "Check ensures clause");
  
  return return_value_sum;
}
```

#### Replacement

Assuming _requires_ and _ensures_ clauses are a sound abstraction of the
behavior of the function *f*, CBMC will use the function contract in place of
the function implementation as follows:

1. Adds assertions for all preconditions specified in the `__CPROVER_requires`
   clauses; 
2. Adds non-deterministic assignments for each symbol listed in the
   `__CPROVER_assigns` clause (see [Assigns Clause](../../contracts/assigns/)
for details);
3. Assumes all postconditions described in the `__CPROVER_ensures` clauses;

In our example, consider that a function `foo` may call `sum`.

```c
int foo()
{
  uint32_t a;
  uint32_t b;
  uint32_t out;
  int rval = sum(a, b, &out);
  if (rval == SUCCESS) 
    return out;
  return rval;
}
```

CBMC will use the function contract in place of the function implementation
wherever the function is called.

```c
int foo()
{
  uint32_t a;
  uint32_t b;
  uint32_t out;
	
  /* Function Contract Replacement */
  /* Precondition */
  __CPROVER_assert(__CPROVER_is_fresh(out, sizeof(*out)), "Check requires clause");
	
  /* Postconditions */
  int return_value_sum = nondet_int();
  __CPROVER_assume(return_value_sum == SUCCESS || return_value_sum == FAILURE);
  __CPROVER_assume((return_value_sum == SUCCESS) ==> (*out == (*a + *b)));

  int rval = return_value_sum;
  if (rval == SUCCESS) 
    return out;
  return rval;
}
```
