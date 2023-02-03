# Memory Predicates {#contracts-memory-predicates}

Back to @ref contracts-user

@tableofcontents

The built-in and user-defined predicates discussed in this section are meant to
let users describe the shape of the memory accessed through pointers in
_requires clauses_ and _ensures clauses_. Attempting to call these predicates
outside of a requires or ensures clause context will result in a verification
error.
## The __CPROVER_is_fresh predicate
### Syntax

```c
bool __CPROVER_is_fresh(void *p, size_t size);
```

To specify memory footprint we use a special function called `__CPROVER_is_fresh `.
The meaning of `__CPROVER_is_fresh` is that we are borrowing a pointer from the
external environment (in a precondition), or returning it to the calling context
(in a postcondition).

#### Parameters

`__CPROVER_is_fresh` takes two arguments: a pointer and an allocation size.
The first argument is the pointer to be checked for "freshness" (i.e., not previously
allocated), and the second is the expected size in bytes for the memory
available at the pointer.

#### Return Value

It returns a `bool` value, indicating whether the pointer is fresh.

### Semantics

To illustrate the semantics for `__CPROVER_is_fresh`, consider the following
implementation of `sum` function.

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

#### Influence of memory allocation failure modes flags in assumption contexts

CBMC models
[memory allocation failure modes](https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/memory-primitives.md#malloc-modelling).
When activated, these modesl result in different
behaviours for `__CPROVER_is_fresh` in assumption contexts (i.e. when used in a
requires clause of a contract being checked against a function, or in an
ensures clause of a contract being used to abstract a function call).

1. **No failure mode** (no flags):
  In this mode, `malloc` and `__CPROVER_is_fresh` never fail
  and will accept a size parameter up to `SIZE_MAX` without triggerring errors.
  However, pointer overflow and assigns clause checking errors will happen any
  time one tries to access such objects beyond an offset of
  `__CPROVER_max_malloc_size` (in bytes), by executing `ptr[size-1]` or
  `ptr[size]` in user-code, or by writing
  `__CPROVER_assigns(__CPROVER_object_from(ptr))` in a contract;
1. **Fail with NULL** (flags: `--malloc-may-fail --malloc-fail-null`):
  In this mode, if `size` is larger than
  `__CPROVER_max_malloc_size`, `malloc` returns a NULL pointer, and imposes an
  implicit assumption that size is less than `__CPROVER_max_malloc_size` when
  returning a non-NULL pointer. `__CPROVER_is_fresh` never fails in assumption
  contexts, so it adds an implicit assumption that `size` is less
  than `__CPROVER_max_malloc_size`.
1. **Fail assert** (flags: `--malloc-may-fail --malloc-fail-assert`):
  In this mode, if `size` is larger
  than `__CPROVER_max_malloc_size`, an `max allocation size exceeded` assertion
  is triggered in `malloc` and execution continues under the assumption that
  `size` is less than `__CPROVER_max_malloc_size`, with `malloc` returning a
  non-NULL pointer. `__CPROVER_is_fresh` never fails in assumption contexts,
  so it will trigger a `max allocation size exceeded` assertion and continue
  execution under the implicit assumption that `size` is less than
  `__CPROVER_max_malloc_size`.

## The __CPROVER_pointer_in_range_dfcc predicate
### Syntax

```c
bool __CPROVER_pointer_in_range_dfcc(void *lb, void *p, void *ub);
```

This predicate holds if `lb`, `p` and `ub` are valid pointers within the same
object and the pointers are ordered such that `lb <= p && p <= ub` holds.

### Semantics
In assertion contexts, the predicate checks the conditions described above.
In assumption contexts, the predicate checks that `lb` and `ub` are valid pointers
into the same object, and updates `p` using a side effect to be a non-deterministic
pointer ranging between `lb` and `ub`.

## User defined memory predicates

Users can write their own memory predicates based on the core predicates described above.
`__CPROVER_is_fresh` allows to specify pointer validity and separation.
`__CPROVER_pointer_in_range` allows to specify aliasing constraints.

For instance, one could write a predicate defining linked lists of at most `len`
elements as follows:

```c
typedef struct list_t
{
  int value;
  struct list_t *next;
} list_t;

// true iff list of len nodes with values in [-10,10]
bool is_list(list_t *l, size_t len)
{
  if(len == 0)
    return l == NULL;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) && -10 <= l->value &&
           l->value <= 10 && is_list(l->next, len - 1);
}
```

One can also simply describe finite nested structures:

```c
typedef struct buffer_t
{
  size_t size;
  char *arr;
  char *cursor;
} buffer_t;

typedef struct double_buffer_t
{
  buffer_t *first;
  buffer_t *second;
} double_buffer_t;

bool is_sized_array(char *arr, size_t size)
{
  return __CPROVER_is_fresh(arr, size);
}

bool is_buffer(buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && (0 < b->size && b->size <= 10) &&
         is_sized_array(b->arr, b->size) &&
}

bool is_double_buffer(double_buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && is_buffer(b->first) &&
         is_buffer(b->second);
}
```

And one can then use these predicates in requires or ensures clauses for function
contracts.

```c
int foo(list_t *l, double_buffer_t *b)
  // clang-format off
  __CPROVER_requires(is_list(l, 3))
  __CPROVER_requires(is_double_buffer(b))
  __CPROVER_ensures(-28 <= __CPROVER_return_value &&
                    __CPROVER_return_value <= 50)
// clang-format on
{
  // access the assumed data structure
  return l->value + l->next->value + l->next->next->value + b->first->size +
         b->second->size;
}
```

### Limitations

The main limitation with user defined predicates are:
- their evaluation must terminate;
- self-recursive predicates are supported, but mutually recursive predicates are
  not supported for the moment.

For instance, in the `is_list` example above, recursion is bounded by the use of
the explicit `len` parameter. The `is_double_buffer` predicate also describes
a bounded structure.

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
