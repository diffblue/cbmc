# Function Pointer Predicates {#contracts-function-pointer-predicates}

Back to @ref contracts-user

@tableofcontents


## Syntax

The function contract language offers the following predicate to specify
preconditions and postconditions about function pointers in _requires clauses_
and _ensures clauses_.

```c
bool __CPROVER_obeys_contract(void (*f)(void), void (*c)(void));
```

Informally, this predicate holds iff function pointer `f` is known to satisfy
contract `c`.

### Parameters

The predicate `__CPROVER_obeys_contract` takes two function pointers as arguments.
The first function pointer must be an lvalue, the second parameter must be a pointer
to a pure contract symbol.

### Return Value

It returns a `bool` value, indicating whether the function pointer is known to
satisfy contract `c`.

## Semantics

To illustrate the semantics of the predicate, let's consider the example below.

The `arr_fun_contract` specifies the class of functions that take a non-`NULL`
array `arr` of size `size` as input and initialise its first element to zero.

The function `foo` takes a possibly `NULL` array `arr` of given `size` and a
possibly `NULL` opaque function pointer `arr_fun`, assumed to satisfy the
contract `arr_fun_contract`.

The function `foo` checks some condition and then calls `arr_fun`.
When `arr_fun` if called, the preconditions of its contract `arr_fun_contract`
will be checked, write set inclusion with respect to the contract of `foo` will
be checked, and its postconditions will be assumed, allowing to establish the
postconditions of `foo`.

```c
// \file fptr.c
#include <stdlib.h>
#include <stdbool.h>

// Type of functions that manipulate arrays of a given size
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
void arr_fun_contract(char *arr, size_t size)
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
;

// Uses a function pointer satisfying arr_fun_contract
int foo(char *arr, size_t size, arr_fun_t arr_fun)
__CPROVER_requires(arr ==> __CPROVER_is_fresh(arr, size))
__CPROVER_requires(arr_fun ==> __CPROVER_obeys_contract(arr_fun, arr_fun_contract))
__CPROVER_assigns(arr && size > 0 && arr_fun : arr[0])
__CPROVER_ensures(__CPROVER_return_value ==> (arr[0] == 0))
{
  if (arr && size > 0 && arr_fun) {
  CALL:
    arr_fun(arr, size);
    return true;
  }
  return false;
}

void main()
{
  size_t size;
  char *arr;
  arr_fun_t arr_fun;
  foo(arr, size, arr_fun);
}
```

### Enforcement

To check that `foo` satisfies its contract, we compile, instrument and analyse the program as follows:

```bash
goto-cc fptr.c
goto-instrument \
--restrict-function-pointer foo.CALL/arr_fun_contract \
--dfcc main \
--enforce-contract foo \
a.out b.out
cbmc b.out
```

The function pointer restriction directive is needed to inform CBMC that we only
expect the contract function `arr_fun_contratt` to be called where `arr_fun`
is called.

We get the following analysis result:

```bash
...

fptr.c function arr_fun_contract
[arr_fun_contract.precondition.1] line 8 Check requires clause of contract contract::arr_fun_contract for function arr_fun_contract: SUCCESS
[arr_fun_contract.assigns.4] line 7 Check that the assigns clause of contract::arr_fun_contract is included in the caller's assigns clause: SUCCESS
[arr_fun_contract.frees.1] line 7 Check that the frees clause of contract::arr_fun_contract is included in the caller's frees clause: SUCCESS

fptr.c function foo
[foo.postcondition.1] line 20 Check ensures clause of contract contract::foo for function foo: SUCCESS
[foo.pointer_dereference.1] line 24 dereferenced function pointer must be arr_fun_contract: SUCCESS

...

** 0 of 72 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

### Replacement

Let's now consider an extended example with two new functions:
- The function `get_arr_fun` returns a pointer to a function satisfying
  `arr_fun_contract`;
- The function bar allocates an array and uses `get_arr_fun` and `foo`
  to initialise it;

Our goal is to check that `bar` satisfies its contract, assuming that `foo`
satisfies its contract and that `get_arr_fun` satisfies its contract.

```c
#include <stdlib.h>

// Type of functions that manipulate arrays of a given size
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
void arr_fun_contract(char *arr, size_t size)
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
;

// Uses a function pointer satisfying arr_fun_contract
int foo(char *arr, size_t size, arr_fun_t arr_fun)
__CPROVER_requires(
  arr ==> __CPROVER_is_fresh(arr, size))
__CPROVER_requires(
  arr_fun ==> __CPROVER_obeys_contract(arr_fun, arr_fun_contract))
__CPROVER_assigns(arr && size > 0 && arr_fun : arr[0])
__CPROVER_ensures(__CPROVER_return_value ==> (arr[0] == 0))
{
  if (arr && size > 0 && arr_fun) {
  CALL:
    arr_fun(arr, size);
    return 1;
  }
  return 0;
}

// Returns a function that satisfies arr_fun_contract
arr_fun_t get_arr_fun()
__CPROVER_ensures(
  __CPROVER_obeys_contract(__CPROVER_return_value, arr_fun_contract))
;

// Creates an array and uses get_arr_fun and foo to initialise it
char *bar(size_t size)
__CPROVER_ensures(
  __CPROVER_return_value ==> size > 0 &&
    __CPROVER_is_fresh(__CPROVER_return_value, size) &&
      __CPROVER_return_value[0] == 0)
{
  if (size > 0) {
    char *arr;
    arr = malloc(size);
    if (arr && foo(arr, size, get_arr_fun()))
      return arr;

    return NULL;
  }
  return NULL;
}

void main()
{
  size_t size;
  char *arr = bar(size);
}
```
We compile, instrument and analyse the program as follows:

```bash
goto-cc fptr.c
goto-instrument \
  --dfcc main \
  --enforce-contract bar \
  --replace-call-with-contract foo \
  --replace-call-with-contract get_arr_fun \
  a.out b.out
cbmc b.out
```

And obtain the following results:

```bash
...

fptr.c function get_arr_fun
[get_arr_fun.assigns.1] line 13 Check that the assigns clause of contract::get_arr_fun is included in the caller's assigns clause: SUCCESS
[get_arr_fun.frees.1] line 13 Check that the frees clause of contract::get_arr_fun is included in the caller's frees clause: SUCCESS

fptr.c function bar
[bar.postcondition.1] line 36 Check ensures clause of contract contract::bar for function bar: SUCCESS

fptr.c function foo
[foo.assigns.7] line 18 Check that the assigns clause of contract::foo is included in the caller's assigns clause: SUCCESS
[foo.frees.1] line 18 Check that the frees clause of contract::foo is included in the caller's frees clause: SUCCESS
[foo.precondition.1] line 20 Check requires clause of contract contract::foo for function foo: SUCCESS
[foo.precondition.2] line 22 Check requires clause of contract contract::foo for function foo: SUCCESS
...

** 0 of 80 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

Proving that `bar` satisfies its contract.

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
- @ref contracts-function-pointer-predicates
- @ref contracts-history-variables
- @ref contracts-quantifiers
