[CPROVER Manual TOC](../../)

# Memory Predicates

### Syntax

```c
bool __CPROVER_is_fresh(void *p, size_t size);
```

To specify memory footprint we use a special function called `__CPROVER_is_fresh `. The meaning of `__CPROVER_is_fresh` is that we are borrowing a pointer from the
external environment (in a precondition), or returning it to the calling context (in a postcondition).

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
