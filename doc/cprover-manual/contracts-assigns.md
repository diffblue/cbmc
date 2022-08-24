[CPROVER Manual TOC](../../)

# Assigns Clause

## In Function Contracts

### Syntax

An _assigns_ clause allows the user to specify a set of locations that may be
assigned to by a function or the body of a loop:

```c
__CPROVER_assigns(*targets*)
```

A function or loop contract contract may have zero or more _assigns_ clauses.

The clause accepts a semicolon-separated list of _conditional target groups_.
A _conditional target group+ consists of an optional _condition_ followed by a
coma-separated list of _targets_.
A _target_ is either an lvalue expression or a call to a function returning
the built-in type `__CPROVER_assignable_t`.

```
targets ::= conditional_target_group (';' conditional_target_group)* (';')?
conditional_target_group ::= (condition ':')? target (',' target)*
target ::= lvalue-expression | call-to-cprover-assignable-t-function
```

The set of locations writable by a function is the union of the locations
specified by the assigns clauses, or the empty set of no _assigns_ clause is
specified.
While, in general, an _assigns_ clause could be interpreted with either
_writes_ or _modifies_ semantics, this design is based on the former.
This means that memory not captured by an _assigns_ clause must not be assigned
to by the given function, even if the value(s) therein are not modified.

### Object slice expressions

The following functions can be used in assigns clauses to specify ranges of assignable bytes.

Given an lvalue expression `expr` with a complete type `expr_t`,
 `__CPROVER_typed_target(expr)` specifies that the range
 of `sizeof(expr_t)` bytes starting at `&expr` is assignable:
```c
__CPROVER_assignable_t __CPROVER_typed_target(expr_t expr);
```

Given a pointer `ptr` pointing into some object `o`,
`__CPROVER_whole_object(ptr)` specifies that all bytes of the object `o`
are assignable:
```c
__CPROVER_assignable_t __CPROVER_whole_object(void *ptr);
```

Given a pointer `ptr` pointing into some object `o`, `__CPROVER_object_from(ptr)`
specifies that the range of bytes starting from the pointer and until the end of
the object `o` are assignable:
```c
__CPROVER_assignable_t __CPROVER_object_from(void *ptr);
```

Given a pointer `ptr` pointing into some object `o`, `__CPROVER_object_upto(ptr, size)`
specifies that the range of `size` bytes of `o` starting at `ptr` are assignable:
The `size` value must such that the range does not exceed the object boundary,
that is, `__CPROVER_object_size(ptr) - __CPROVER_pointer_offset(ptr) >= size` must hold:

```c
__CPROVER_assignable_t __CPROVER_object_upto(void *ptr, __CPROVER_size_t size);
```

CAVEAT: The ranges specified by `__CPROVER_whole_object`,
`__CPROVER_object_from` and `__CPROVER_object_upto` must *not*
be interpreted as pointers by the program. This is because during
call-by-contract replacement, `__CPROVER_havoc_slice(ptr, size)` is used to
havoc these byte ranges, and `__CPROVER_havoc_slice` does not support
havocing pointers. `__CPROVER_typed_target` must be used to specify targets
that are pointers.

### Specifying parameterized and reusable sets of assignable locations

Users can specify sets of assignable locations by writing their own functions
returning the built-in type `__CPROVER_assignable_t`.

Such functions may call other functions returning `__CPROVER_assignable_t` (built-in or user-defined).
These functions must ultimately be side-effect free, deterministic and loop-free,
or can contain loops that must be unwound to completion using a preliminary
`goto-instrument --unwindset` pass.

For example, the following function declares even cells of `arr` up to index `10`
as assignable:

```c
__CPROVER_assignable_t assign_even_upto_ten(int *arr, size_t size)
{
   assert(arr && size > 10);
   __CPROVER_typed_target(arr[0]);
   __CPROVER_typed_target(arr[2]);
   __CPROVER_typed_target(arr[4]);
   __CPROVER_typed_target(arr[6]);
   __CPROVER_typed_target(arr[8]);
   __CPROVER_typed_target(arr[10]);
}
```

This function other defines a conditional set of assignable locations,
and calls the function `assign_even_upto_ten`.

```c
__CPROVER_assignable_t my_assignable_set(int *arr, size_t size)
{
   if (arr && 0 < size)
      __CPROVER_typed_target(arr[0]);

   if (arr && 5 < size && size < 10)
      __CPROVER_object_upto(arr, 5 * sizeof(int));

   if (arr && 10 < size)
      assign_even_upto_ten(arr, 5 * sizeof(int));
}
```

An assigns clause target can consist of a call to a function returning
`__CPROVER_assignable_t`:

```c
int foo(int *arr, size_t size)
__CPROVER_requires(!arr || __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(my_assignable_set(arr, size))
__CPROVER_ensures(true)
{ ... }
```

When checking a function contract at some call-site or
(loop contract at some program location), these `__CPROVER_assignable_t`
functions are evaluated and any target they describe gets added to
the write set. If a function call is not reachable according to the control flow
the target does not get added to the write set.

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
implementation as described by
[Requires \& Ensures Clauses](../../contracts/requires-and-ensures/#replacement), and it will add
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
