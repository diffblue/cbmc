# Memory Predicates {#contracts-memory-predicates}

Back to @ref contracts-user

@tableofcontents

The built-in predicates discussed in this section are used to describe pointer
properties in _requires clauses_ and _ensures clauses_.

At a basic level the predicates allow to specify pointers to fresh objects
(i.e. allocated and distinct, `__CPROVER_is_fresh(p, size)`), of aliased pointers
(`__CPROVER_pointer_equals(p, q)`), or pointers ranging over pointer intervals
(`__CPROVER_pointer_in_range_dfcc(lb, p, ub)`).

They can only be used in the context of a requires and ensures clauses, any
attempt to call these predicates outside of a requires or ensures clause will
result in a verification error.

Pointer predicates can be used with conjunctions, implications or disjunctions
to describe richer data structures where some parts are only conditionally
allocated, but requires and ensures clauses must not attempt to establish more
than one predicate at the same time for a same pointer.

One can build their own pointer predicates using these built-in predicates,
to describe (bounded) linked data structures such as buffers, lists, etc.

## The __CPROVER_pointer_equals predicate

This predicate checks for pointer validity and equality.

```c
bool __CPROVER_pointer_equals(void *p, void *q);
```

This predicate checks for pointer validity and equality.

It returns:
- `true` if and only if:
  -  `p` is either `NULL` or valid,
  -  `q` is either `NULL` of valid,
  -  `p` is equal to `q`.

When checking a function against a contract (`--enforce-contract`):
- in a _requires_ clause, the predicate will check that `q` is always
  either `NULL` or valid, and it will assign `p` with `q`. This results in a state
  where both pointers are either `NULL` or valid and are equal;
- used in an _ensures_ clause it will check that both `p` and `q` are either
  NULL or valid, and that `p == q`.

When replacing a function call by a contract (`--replace-call-with-contract`):
we get the dual behaviour:
- used in a _requires_ clause it will check that both `p` and `q` are either
  NULL or valid, and that `p == q`.
- in an _ensures clause, the predicate will check that `q` is always
  either `NULL` or valid, and it will assign `p` with `q`. This results in a state
  where both pointers are either `NULL` or valid and are equal;

## The __CPROVER_is_fresh predicate

The predicate `__CPROVER_is_fresh `  takes a pointer `p` and an allocation
size `size` and checks pointer validity and separation with other fresh pointers.

```c
bool __CPROVER_is_fresh(void *p, size_t size);
```

The predicate `__CPROVER_is_fresh(p, n)` holds when `p` points into a valid
object with at least `n` bytes available after the pointer, and the object
pointed to by `p` is distinct from all other objects pointed to in other
`__CPROVER_is_fresh(q, m)` found in the requires and ensures clauses.

When checking a function against a contract (`--enforce-contract`):
- `__CPROVER_is_fresh` in the `requires` clause works like a nondeterministic
  `p = malloc(size)` (separation is assured by construction);
- `__CPROVER_is_fresh` in the `ensures` clause checks pointer validity and
  separation against other `__CPROVER_is_fresh` occurrences in the `requires`
  clause and the `ensures` clause.

When replacing a function call by a contract (`--replace-call-with-contract`):
- `__CPROVER_is_fresh` in the `requires` clause checks pointer validity and
  separation against other `__CPROVER_is_fresh` occurrences in the `requires`
  clause;
- `__CPROVER_is_fresh` in the `ensures` clause works like a nondeterministic
  `p = malloc(size)` (separation is assured by construction);

## The __CPROVER_pointer_in_range_dfcc predicate
### Syntax

This predicate holds if pointers `lb`, `p` and `ub` are valid pointers, pointing
within the same object and the condition `lb <= p && p <= ub` holds.

```c
bool __CPROVER_pointer_in_range_dfcc(void *lb, void *p, void *ub);
```

When checking a function against a contract (`--enforce-contract`):
- In the `requires` clause, `__CPROVER_pointer_in_range_dfcc` checks that `lb`
  and `ub` are valid and point into the same object, and nondeterministically
  assigns `p` to a nondet pointer between `lb` and `ub`;
- In the `ensures` clause, `__CPROVER_pointer_in_range_dfcc` checks that `lb`
  and `ub` are valid and point into the same object, that `p` is between `lb`
  and `ub`;

When replacing a function call by a contract (`--replace-call-with-contract`):
- In the `requires` clause, `__CPROVER_pointer_in_range_dfcc` checks that `lb`
  and `ub` are valid and point into the same object, that `p` is between `lb`
  and `ub`;
- In the `ensures` clause, `__CPROVER_pointer_in_range_dfcc` checks that `lb`
  and `ub` are valid and point into the same object, and nondeterministically
  assigns `p` to a nondet pointer between `lb` and `ub`;

## Using memory predicates in disjunctions

It is possible to use memory predicates in disjunctions to describe alternatives.

For instance, to specify a conditionally allocated pointer, the implication
 `==>` operator can be used.

The `array` pointer is only valid when len is in some bounds, otherwise nothing
is assumed about `array` and the pointer is considered _invalid_, i.e. any
attempt to use it by the program under verification will result in an error.

```C
int foo(int *array, size_t len)
__CPROVER_requires(
  (len < INT_MAX/sizeof(int) && len > 0)
      ==> __CPROVER_is_fresh(array, len*sizeof(int)))
{
   ...
}
```

In this other example, the function takes two pointers `a` and `b` and a
and sets `*out` to the longest one:

```C
void foo(int *a, size_t len_a, int *b, size_t len_b, int **out)
__CPROVER_requires(__CPROVER_is_fresh(a, len_a * sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, len_b * sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(int *)))
__CPROVER_assigns(*out)
__CPROVER_requires(len_a >= len_b ==> __CPROVER_pointer_equals(*out, a))
__CPROVER_requires(len_a < len_b ==> __CPROVER_pointer_equals(*out, b))
{
   ...
}
```

In last other example, the function takes two pointers `a` and `b` and a
and sets `*out` to either `a` or `b`, nondeterministically:

```C
void foo(int *a, int *b, int **out)
__CPROVER_requires(__CPROVER_is_fresh(a, 1)) // at least one byte
__CPROVER_requires(__CPROVER_is_fresh(b, 1))
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(int *)))
__CPROVER_assigns(*out)
__CPROVER_requires(
  __CPROVER_pointer_equals(*out, a) || __CPROVER_pointer_equals(*out, b))
{
   ...
}
```

## Writing your own memory predicates

One can write their own memory predicates based on the built-in predicates.


One can specify (finite) nested structures:

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

One can even describe inductively defined (but bounded) structures such as lists:

```c
typedef struct list_t
{
  int value;
  struct list_t *next;
} list_t;

bool value_in_range(int lb, int value, int ub) {
  return lb <= value && value <= ub;
}

bool is_list(list_t *l, size_t len)
{
  if(len == 0) {
    // list size bounded by `len`
    return __CPROVER_pointer_equals(l,  NULL);
  } else {
    // either NULL or some fresh node
    if (__CPROVER_pointer_equals(l,  NULL)) {
      return true;
    } else {
      return __CPROVER_is_fresh(l, sizeof(*l)) &&
        value_in_range(-10, l->value, 10) &&
        is_list(l->next, len - 1);
    }
  }
}
```

And use these predicates in requires/ensures clauses:

```c
// take a list and a double buffer and sum list values and buffer sizes
int foo(list_t *l, double_buffer_t *b)
  // clang-format off
  __CPROVER_requires(is_list(l, 3))
  __CPROVER_requires(is_double_buffer(b))
  __CPROVER_ensures(-28 <= __CPROVER_return_value && __CPROVER_return_value <= 50)
// clang-format on
{
  // access the assumed data structure
  return l->value + l->next->value + l->next->next->value + b->first->size +
         b->second->size;
}
```

Internally, CBMC instruments these user-defined predicates to turn them into
- nondeterministic allocators that build the data structures when used in
  assumption contexts;
- checker functions that can walk a pointer structure and check pointer validity
  and separation/aliasing/interval constraints in assertion contexts.

### Limitations

The main limitation with user defined predicates are:
- their evaluation must terminate;
  - For instance, in the `is_list` example above, recursion is bounded using
  use of the explicit `len` parameter.
  - The `is_double_buffer` predicate also describes a bounded structure.
- mutually-recursive predicates are not supported for the moment.


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
