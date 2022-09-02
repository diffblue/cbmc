[CPROVER Manual TOC](../../)

# Function Contracts

CBMC offers support for function contracts, which includes the following types of clauses:
- _requires clauses_ specify preconditions,
- _requires contract clauses_ specify preconditions on function pointers,
- _ensures clauses_ specify postconditions,
- _ensures contract clauses_ specify postconditions on function pointers,
- _assigns clauses_ specify memory locations that may be assigned to by the function,
- _frees clauses_ specify pointers that may be freed by the function.

These clauses allow to describe the specification of a function formally.
CBMC also provides a series of built-in constructs to be used with functions
contracts (e.g., _history variables_, _quantifiers_, _memory predicates_, etc.).

## Overview

Take a look at the example below.

```c
#include <stdlib.h>
#include <stdint.h>

#define SUCCESS 0
#define FAILURE -1

int sum(const uint32_t a, const uint32_t b, uint32_t* out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}

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

Function `sum` writes the sum of `a` and `b` to `out`, and returns `SUCCESS`;
unless the result of the addition is too large to be represented as an `uint32_t`, in which case it returns `FAILURE`. Let's write
a function contract for this function.

A function contract has 4 parts:

- **Preconditions** - describes requirements on the arguments supplied by the caller and on global variables;
- **Postconditions** - describes the effects of the function;
- **Assignable Set** - describes the set of memory locations the function is allowed to assign to;
- **Freeable Set** - describes the set of pointers the function is allowed to free.

In our example, the developer may require from the caller to properly allocate
all arguments, thus, pointers must be valid. We can specify the preconditions of
a function using `__CPROVER_requires` (see [Requires \& Ensures
Clauses](../../contracts/requires-and-ensures/) for details) and we can
specify an allocated object using a predicate called `__CPROVER_is_fresh` (see
[Memory Predicate](../../contracts/memory-predicates/) for details). Thus, for the `sum` function, the set
of preconditions are

```c
/* Precondition */
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
```

We can use `__CPROVER_ensures` to specify postconditions (see [Requires \&
Ensures Clauses](../../contracts/requires-and-ensures/) for details).  In our
example, developers can use the built-in construct `__CPROVER_return_value`,
which represents the return value of a function. As postconditions, one may list
possible return values (in this case, either `SUCCESS` or `FAILURE`) as well as
describe the main property of this function: if the function returns `SUCCESS`,
then `*out` stores the result of `a + b`.  We can also check that the value in
`*out` will be preserved in case of failure by using `__CPROVER_old`, which
refers to the value of a given object in the pre-state of a function (see
[History Variables](../../contracts/history-variables/) for details). Thus, for the `sum` function, the
set of postconditions are


```c
/* Postconditions */
__CPROVER_ensures(__CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures((__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
__CPROVER_ensures((__CPROVER_return_value == FAILURE) ==> (*out == __CPROVER_old(*out)))
```

Finally, the _assigns_ clause allows developers to define a frame condition (see
[Assigns Clause](../../contracts/assigns/) for details).
In general, systems for describing the frame condition of a function
use either writes or modifies semantics; this design is based on the former.
This means that memory not specified by the assigns clause must
not be written within the given function scope, even if the value(s) therein are
not modified. In our example, since we expect that only the value that
`out` points to may be modified, we annotate the function using `__CPROVER_assigns(*out)`.

```c
/* Write Set */
__CPROVER_assigns(*out)
```

Here is the whole function with its contract.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Precondition */
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
/* Postconditions */
__CPROVER_ensures(__CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures((__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
__CPROVER_ensures((__CPROVER_return_value == FAILURE) ==> (*out == __CPROVER_old(*out)))
/* Write Set */
__CPROVER_assigns(*out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}
```

First, we have to prove that the function satisfies the contract.

```shell
   goto-cc -o sum.goto *.c --function sum
   goto-instrument --enforce-contract sum sum.goto sum-checking-contracts.goto
   cbmc sum-checking-contracts.goto --function sum
```

The first command just compiles the GOTO program as usual, the second command
instruments the code to check the function satisfies the contract,
and the third one runs CBMC to do the checking.

In order to start the analysis in an arbitrary state when a function contract
gets checked, the contract instrumentation pass automatically havocs all static
variables of the program. To avoid havocing certain static variables,
the command line switch `--nondet-static-exclude name-of-variable` can be passed
to `goto-instrument` in addition to the other swtiches specifying the contract
to check.

Now that we have proved that the function satisfies the contract, we can use the function
contract in place of the function implementation wherever the function is
called.

```shell
   goto-cc -o foo.goto *.c --function foo
   goto-instrument --replace-call-with-contract sum foo.goto foo-using-sum-contract.goto
   cbmc foo-using-sum-contract.goto --function foo
```

The first command just compiles the GOTO program as usual, the second command
instruments the code to use the function contract in place of the function
implementation wherever is invoked, and the third one runs CBMC to check the
program using contracts.

## Additional Resources

- [Requires \& Ensures Clauses](../../contracts/requires-and-ensures/)
- [Assigns Clause](../../contracts/assigns/)
- [Memory Predicates](../../contracts/memory-predicates/)
- [History Variables](../../contracts/history-variables/)
- [Quantifiers](../../contracts/quantifiers/)
