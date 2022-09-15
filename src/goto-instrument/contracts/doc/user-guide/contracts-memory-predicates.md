[CPROVER Manual TOC](../../)

# Memory Predicates

### Syntax

To specify memory footprint we provide the built-in function `__CPROVER_is_fresh`.

```c
bool __CPROVER_is_fresh(const void *p, size_t size);
```

When used in a precondition, `__CPROVER_is_fresh(p, s)` expresses that the contract
is expecting `p` to be a pointer to a fresh object of size at least `s` provided
by the calling context. In a postcondition, `__CPROVER_is_fresh(p, s)` expresses
that the function returns a pointer to a fresh object to the calling context.
From the perspective of the contract, and object is _fresh_ if and only if it is
distinct from any other object seen by any other occurrences of
`__CPROVER_is_fresh` in the same contract.

When asserting a precondition (in contract replacement mode) or asserting a
postcondition (in contract checking mode), a call to `__CPROVER_is_fresh(p, s)`
returns true if and only if `p` points to and object distinct from any other
object seen by another occurrence of `__CPROVER_is_fresh(p', s')` (in either
preconditions or post-conditions).

When assuming a postcondition (in contract replacement mode) or assuming a
precondition (in contact enforcement mode), a call to `__CPROVER_is_fresh(p, s)`
gets translated to a statement `p = malloc(s)` which ensures that `p` points to
an object distinct from any other object.

The predicate `__CPROVER_is_freshr ` has the same meaning as
`__CPROVER_is_fresh` but takes its pointer parameter by reference:

```c
bool __CPROVER_is_freshr(const void **p, size_t size);
```

This allows `__CPROVER_is_freshr` to be called from within functions and still
check or update the desired pointer:

```c
// a function specifying that `arr` must be fresh
bool foo_preconditions(const char **arr, const size_t size) {
  return __CPROVER_is_freshr(arr, size);
}

int foo(char *arr, size_t size)
// call if from the requires clause, checks or updates arr as seen
// by foo
__CPROVER_requires(foo_preconditions(&arr, size))
{
  for(size_t i = 0; i < size ; i ++)
    arr[i] = i;
}
```
### Parameters

`__CPROVER_is_fresh` takes two arguments: a pointer and an allocation size.
The first argument is the pointer to be checked for "freshness" (i.e., not previously
allocated), and the second is the expected size in bytes for the memory
available at the pointer.

### Return Value

It returns a `bool` value, indicating whether the pointer is fresh.

### Semantics

To illustrate the semantics for `__CPROVER_is_fresh`, consider the following implementation of `sum` function.

```c
int *err_signal; // Global variable

void sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
__CPROVER_ensures(__CPROVER_is_fresh(err_signal, sizeof(*err_signal)))
__CPROVER_assigns(*out, err_signal)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  err_signal = malloc(sizeof(*err_signal));
  if (!err_signal) return;
  if (result > UINT32_MAX) *err_signal = FAILURE;
  *out = (uint32_t) result;
  *err_signal = SUCCESS;
}
```

#### Enforcement

When checking the contract abstracts a function a `__CPROVER_is_fresh`
in a _requires_ clause will cause fresh memory to be allocated.
In an _ensures_ clause it will check that memory was freshly allocated.

```c
int *err_signal; // Global variable

int __CPROVER_contracts_original_sum(const uint32_t a, const uint32_t b, uint32_t* out)
{	 
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  err_signal = malloc(sizeof(*err_signal));
  if (!err_signal) return;
  if (result > UINT32_MAX) *err_signal = FAILURE;
  *out = (uint32_t) result;
  *err_signal = SUCCESS;
}

/* Function Contract Enforcement */
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
{
  __CPROVER_assume(__CPROVER_is_fresh(out, sizeof(*out))); // Assumes out is freshly allocated
  int return_value_sum = __CPROVER_contracts_original_sum(a, b, out);
  __CPROVER_assert(__CPROVER_is_fresh(err_signal, sizeof(*err_signal)), "Check ensures clause");
  return return_value_sum;
}
```

#### Replacement

In our example, consider that a function `foo` may call `sum`.

```c
int *err_signal; // Global variable

int foo()
{
  uint32_t a;
  uint32_t b;
  uint32_t out;
  sum(a, b, &out);
  return *err_signal;
}
```

When using a contract as an abstraction in place of a call to the function
a `__CPROVER_is_fresh` in a _requires_ clause will check that the argument
supplied is fresh and `__CPROVER_is_fresh` in an _ensures_ clause will
result in a fresh malloc.

```c
int *err_signal; // Global variable

int foo()
{
  uint32_t a;
  uint32_t b;
  uint32_t out;
	
  /* Function Contract Replacement */
  /* Precondition */
  __CPROVER_assert(__CPROVER_is_fresh(out, sizeof(*out)), "Check requires clause");
	
  /* Writable Set */
  *(&out) = nondet_uint32_t();
  err_signal = nondet_int_pointer();
	
  /* Postconditions */
  __CPROVER_assume(__CPROVER_is_fresh(err_signal, sizeof(*err_signal))); // Assumes out is allocated

  return *err_signal;
}
```
