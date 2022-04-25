# Assigns Clause

## In Function Contracts

### Syntax

```c
__CPROVER_assigns(*identifier*, ...)
```

An _assigns_ clause allows the user to specify that a memory location may be written by a function. The set of locations writable by a function is the union of the locations specified by the assigns clauses, or the empty set of no _assigns_ clause is specified. While, in general, an _assigns_ clause could be interpreted with either _writes_ or _modifies_ semantics, this
design is based on the former. This means that memory not captured by an
_assigns_ clause must not be written within the given function, even if the
value(s) therein are not modified.

### Object slice expressions

The following functions can be used in assigns clause to specify ranges of 
assignable addresses.

Given a pointer `ptr` pointing into some object `o`, `__CPROVER_object_from(ptr)` 
specifies that all bytes starting from the given pointer and until the end of 
the object are assignable:
```c
__CPROVER_size_t __CPROVER_object_from(void *ptr); 
```

Given a pointer `ptr` pointing into some object `o`, `__CPROVER_object_from(ptr, size)` 
specifies that `size` bytes starting from the given pointer and until the end of the object are assignable.
The `size` value must such that `size <= __CPROVER_object_size(ptr) - __CPROVER_pointer_offset(ptr)` holds:

```c
__CPROVER_size_t __CPROVER_object_slice(void *ptr, __CPROVER_size_t size);
```

Caveats and limitations: The slices in question must *not*
be interpreted as pointers by the program. During call-by-contract replacement, 
`__CPROVER_havoc_slice(ptr, size)` is used to havoc these targets, 
and `__CPROVER_havoc_slice` does not support havocing pointers. 
### Parameters

An _assigns_ clause currently supports simple variable types and their pointers,
structs, and arrays.  Recursive pointer structures are left to future work, as
their support would require changes to CBMC's memory model.

```c
/* Examples */
int err_signal; // Global variable

int sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_assigns(*out)

int sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_assigns(err_signal)

int sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_assigns(*out, err_signal)
```

### Semantics

The semantics of an _assigns_ clause of a given function can be understood
in two contexts: enforcement and replacement.

#### Enforcement

In order to determine whether an _assigns_ clause is a sound abstraction of
the write set of a function *f*, the body of the function is instrumented with
assertion statements before each statement which may write to memory (e.g., an
assignment).  These assertions are based on the writable locations identified by the _assigns_ clauses.

For example, consider the following implementation of `sum` function.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Writable Set */
__CPROVER_assigns(*out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}
```

Assignable variables in the function are just those specified so with
`__CPROVER_assigns`, together with any local variables.
In the case of `sum` that is `*out` and `result`.  Each assignment will be
instrumented with an assertion to check that the target of the assignment
is one of those options.

```c
int __CPROVER_contracts_original_sum(const uint32_t a, const uint32_t b, uint32_t* out)
{
  const uint64_t result;
  __CPROVER_assert((__CPROVER_POINTER_OBJECT(&result) == __CPROVER_POINTER_OBJECT(out)  &&
                    __CPROVER_POINTER_OFFSET(&result) == __CPROVER_POINTER_OFFSET(out)) ||
                   (__CPROVER_POINTER_OBJECT(&result) == __CPROVER_POINTER_OBJECT(&result)  &&
                    __CPROVER_POINTER_OFFSET(&result) == __CPROVER_POINTER_OFFSET(&result))
                   , "Check that result is assignable");
  result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  __CPROVER_assert((__CPROVER_POINTER_OBJECT(out) == __CPROVER_POINTER_OBJECT(out)  &&
                     __CPROVER_POINTER_OFFSET(out) == __CPROVER_POINTER_OFFSET(out)) ||
                    (__CPROVER_POINTER_OBJECT(out) == __CPROVER_POINTER_OBJECT(&result)  &&
                     __CPROVER_POINTER_OFFSET(out) == __CPROVER_POINTER_OFFSET(&result))
                    , "Check that result is assignable");
  *out = (uint32_t) result;
  return SUCCESS;
}

/* Function Contract Enforcement */
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
{
  int return_value_sum = __CPROVER_contracts_original_sum(a, b, out);
  return return_value_sum;
}
```

Additionally, the set of assignable target expressions is updated while
traversing the function body when new memory is allocated.  For example, the
statement `x = (int *)malloc(sizeof(int))` would create a pointer, stored in
`x`, to assignable memory. Since the memory is allocated within the current
function, there is no way an assignment to this memory can affect the memory of
the calling context.  If memory is allocated for a struct, the subcomponents are
considered assignable as well.

Finally, a set of freely-assignable symbols *free* is tracked during the
traversal of the function body. These are locally-defined variables and formal
parameters without dereferences.  For example, in a variable declaration `<type>
x = <initial_value>`, `x` would be added to the *free* set. Assignment statements
where the left-hand-side is in the *free* set are not instrumented with the above assertions.

#### Replacement

Assuming _assigns_ clauses are a sound abstraction of the write set for
a given function, CBMC will use the function contract in place of the function
implementation as described by [Requires \& Ensures
Clauses](contracts-requires-and-ensures.md) - Replacement section, and it will add
non-deterministic assignments for each object listed in the `__CPROVER_assigns`
clause. Since these objects might be modified by the function, CBMC uses
non-deterministic assignments to havoc them and restrict their values only by
assuming the postconditions (i.e., ensures clauses).

In our example, consider that a function `foo` may call `sum`.

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Preconditions */
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
/* Postconditions */
__CPROVER_ensures(__CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures((__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
/* Writable Set */
__CPROVER_assigns(*out)
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
	
  /* Writable Set */
  *(&out) = nondet_uint32_t();
	
  /* Postconditions */
  int return_value_sum = nondet_int();
  __CPROVER_assume(return_value_sum == SUCCESS || return_value_sum == FAILURE);
  __CPROVER_assume((return_value_sum == SUCCESS) ==> (*out == (a + b)));

  int rval = return_value_sum;
  if (rval == SUCCESS) 
    return out;
  return rval;
}
```

## In Loop Contracts

TODO: Document `__CPROVER_assigns` for loops.
