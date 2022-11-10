# Requires and Ensures Clauses {#contracts-requires-ensures-contract}

Back to @ref contracts-user

@tableofcontents

## Syntax

```c
__CPROVER_requires_contract(function_pointer, contract_id (, NULL)?)
```

A _requires contract_ clause specifies the precondition that a function pointer
points to a function satisfying a given contract, or is optionally NULL.

```c
__CPROVER_ensures_contract(function_pointer, contract_id (, NULL)?)
```

A _ensures contract_ clause specifies the postcondition that a function pointer
points to a function satisfying a given contract, or is optionally NULL.

## Semantics

The semantics of _requires contract_ and _ensures contract_ clauses can be
understood in two contexts: enforcement and replacement.

To illustrate these two perspectives, consider the following program:

```c
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef int (*fun_t)(int);

int add_one(int x)
__CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(x) + 1);

// returns either a pointer to a function that satisfies add_one or NULL
fun_t get_add_one()
__CPROVER_ensures_contract(__CPROVER_return_value, add_one);

int foo(fun_t f_in, int x, fun_t *f_out)
__CPROVER_requires_contract(f_in, add_one, NULL)
__CPROVER_assigns(*f_out)
__CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(x) + 1)
__CPROVER_ensures_contract(*f_out, add_one)
{
  if (f_in)
  {
    *f_out = f_in;
  }
  else
  {
    *f_out = get_add_one();
  }

CALL:
  return (*f_out)(x);
}

int main()
{
  fun_t f_in;
  int x;
  fun_t f_out;
  foo(f_in, x, &f_out);
CALL:
  __CPROVER_assert(f_out(1) == 2, "f_out satisfies add_one");
}
```

The function `add_one` is a contract that describes a function that adds one
to its input.
The function `get_add_one` is a contract that describes a function returning a
pointer to a function satisfying the contract `add_one`.

The Function `foo` takes a function pointer `f_in` as input and requires that
it either satisfies `add_one` or is NULL;
If `f_in` is not NULL, `foo` set `f_out` to `f_in`;
If `f_in` is NULL, `foo` calls `get_add_one` to set `f_out`  to a non-NULL
  pointer to a function that satisfies `add_one`;
The function `foo` returns the result of applying `f_out` to its input, which
allows to establish its post condition.
The `main` function calls `f_out(1)` and checks if the `add_one` contract holds
for this particular input.

This program is instrumented using the following commands:

```
goto-cc main.c -o a.out
goto-instrument --dfcc main --restrict-function-pointer foo.CALL/add_one --restrict-function-pointer main.CALL/add_one --enforce-contract foo --replace-call-with-contract get_add_one a.out b.out
```

The function pointer restrictions are let CBMC know that the function pointers
in `foo` and `main` must be pointing to the function `add_one`, which serves as
the cannonical representation of the assumed contract. These assumptions will be
checked by CBMC, i.e. if it is possible that the function pointer points to
another function the analysis will fail.

The analysis results are the following:

```
cbmc b.out

...

main.c function foo
[foo.postcondition.1] line 15 Check ensures clause of contract contract::foo for function foo: SUCCESS
[foo.postcondition.2] line 16 Assert function pointer '*f_out_wrapper' obeys contract 'add_one': SUCCESS
[foo.assigns.1] line 18 Check that *f_out is assignable: SUCCESS
[foo.assigns.3] line 20 Check that *f_out is assignable: SUCCESS
[foo.pointer_dereference.1] line 22 dereferenced function pointer must be add_one: SUCCESS

main.c function main
[main.assertion.1] line 31 f_out satisfies add_one: SUCCESS
[main.pointer_dereference.1] line 31 dereferenced function pointer must be add_one: SUCCESS

** 0 of 56 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

### Enforcement

When enforcing a contract, a clause

```c
__CPROVER_requires(function_pointer, contract_id, NULL)
```

is turned into a non-deterministic assignment and inserted before the call site
of the function under verification:


```c
function_pointer = nondet() ? &contract_id : NULL;
```

That way, the function under verification receives a pointer to the
`contract_id` function. The instrumentation pass also generates a body for the
function `contract_id` from its contract clauses, so it becomes the canonical
representation of the contract.

An _ensures contract_ clause:

```c
__CPROVER_ensures(function_pointer, contract_id, NULL)
```

is turned into an assertion:

```c
assert(function_pointer ==> function_pointer == &contract_id);
```

That checks that whenever the `function_pointer` is not null, it points to the
function `contract_id`, the canonical representation of the contract.

### Replacement

For contract replacement, the dual transformation is used: _requires contract_
clauses are turned into assertions, and _ensures contract_ clauses are turned
into nondeterministic assignments.

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
