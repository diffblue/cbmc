# Assigns Clauses {#contracts-assigns}

Back to @ref contracts-user

@tableofcontents

## Syntax

An _assigns_ clause allows the user to specify a set of locations that may be
assigned to by a function or the body of a loop:

```c
__CPROVER_assigns(targets)
```

Where `targets` has the following syntax:

```
targets           ::= cond-target-group (';' cond-target-group)* ';'?
cond-target-group ::= (condition ':')? target (',' target)*
target            ::= lvalue-expr
                    | __CPROVER_typed_target(lvalue-expr)
                    | __CPROVER_object_whole(ptr-expr)
                    | __CPROVER_object_from(ptr-expr)
                    | __CPROVER_object_upto(ptr-expr, uint-expr)
```

The set of locations writable by a function is the union of the sets of locations
specified by its assigns clauses, or the empty set if no _assigns_ clause is
specified.
While, in general, an _assigns_ clause could be interpreted with either
_writes_ or _modifies_ semantics, this design is based on the former.
This means that memory not captured by an _assigns_ clause must not be assigned
to by the given function, even if the value(s) therein are not modified.

For function contracts, the condition and target expressions
in the assigns clause may only involve function parameters,
global variables or type identifiers (in `sizeof` or cast expressions).
The target expression must be free of function calls and side-effects.
The condition expression may contain calls to side-effect-free functions.

For a loop contract, the condition and target expressions in the assigns clause
may involve any identifier that is in scope at loop entry
(parameters of the surrounding function, local variables, global variables,
type identifiers in `sizeof` or cast expressions, etc.).
The target expression must be free of function calls and side-effects.
The condition expression may contain calls to side-effect-free functions.

### Lvalue targets

Roughly speaking, _lvalues_ are expressions that are associated with a memory
location, the address of which can be computed using the address-of operator
`&`.

Examples of lvalues are: `x` if `x` is either a global or local variable
identifier, `*ptr` if `ptr` is a pointer expression, `ptr[i]` or `ptr + i` if
`ptr` is pointer variable or an array and `i` is an integer expression, etc.

Examples of non-lvalues: literal constants like `0`, `1`, ..., arithmetic
expressions like `x + y` when `x` and `y` are both arithmetic variables,
function pointer expressions, etc.

An lvalue target `expr` with a complete type `expr_t` specifies that the range
starting at `&expr` and of size `sizeof(expr_t)` bytes is assignable.

Lvalues can also be wrapped in `__CPROVER_typed_target` with the same
meaning: for an lvalue `expr` with a complete type `expr_t`,
`__CPROVER_typed_target(expr)` specifies that the range of `sizeof(expr_t)`
bytes starting at `&expr` is assignable:

```c
void __CPROVER_typed_target(expr_t expr);
```

In order to specify that a memory location the contents of which is interpreted
as a pointer by the program is assignable, one must use the notation
`__CPROVER_assigns(ptr)` or the equivalent
`__CPROVER_assigns(__CPROVER_typed_target(ptr))`, as opposed to the slice
operators `__CPROVER_object_whole`, `__CPROVER_object_from`,
or `__CPROVER_object_upto`.
This ensures that during call-by-contract replacement the memory location gets
turned into a non-deterministic pointer.

For instance:

```c
struct circular_buffer_t {
  int *first;
  int *last;
  int *current;
}

void step(struct circular_buffer_t *buf)
// correct
__CPROVER_assigns(__CPROVER_typed_target(buf->current))
// not correct
__CPROVER_assigns(__CPROVER_object_upto(&(buf->current), sizeof(buf->current))
{
  if(buf->current == buf->last)
    buf->current = buf->first;
  else
    buf->current += 1;
}
```

### Object slice targets

```c
void __CPROVER_object_upto(void *ptr, __CPROVER_size_t size);
```

Given a pointer `ptr` pointing into some object (possibly at some non-zero offset),
`__CPROVER_object_upto(ptr, size)` specifies that the range of `size` bytes starting
at `ptr` is assignable.


The value of `size` must such that the range does not exceed
the object's boundary, i.e.
`size <= __CPROVER_OBJECT_SIZE(ptr) - __CPROVER_POINTER_OFFSET(ptr)` must hold
(otherwise an assertion violation will occur and make the whole analysis fail).

In the example below, the `struct vect_t`, its `data` array and an exta hidden
byte are packed together in a single object by the `vec_alloc` function.
The `vec_clear` function can only assign `vec->size` bytes starting from
`vec->data`. As a result the assignments to `vec->size` and the hidden byte
fail the verification.

```c
#include <stdlib.h>

#define MAX_SIZE 10

struct vec_t {
  size_t size;
  char *data;
};

// Allocates a vect_t struct together with its data and a hidden byte
// in a same object.
struct vec_t *vec_alloc(size_t size) {

  if(size > MAX_SIZE)
    size = MAX_SIZE;

  // allocate the struct + data + 1 extra hidden byte
  struct vec_t *vec = malloc(sizeof(struct vec_t) + size + 1);
  if (vec) {
    vec->size = size;
    vec->data = ((char *)vec) + sizeof(struct vec_t);
  }
  return vec;
}

// Clear the vec->data array
void vec_clear(struct vec_t *vec)
  __CPROVER_assigns(
    vec && vec->data: __CPROVER_object_upto(vec->data, vec->size))
{
  if (!vec)
    return;

  vec->size = vec->size; // FAILURE

  for (size_t i = 0; i < vec->size; i++)
    vec->data[i] = 0; // SUCCESS

  char *hidden_byte = ((char *)vec + sizeof(*vec) + vec->size);
  *hidden_byte = 0; // FAILURE
}

// Proof harness
int main() {
  size_t size;
  struct vec_t *vec = vec_alloc(size);
  vec_clear(vec);
}
```

---

```c
void __CPROVER_object_from(void *ptr);
```

Given a pointer `ptr` pointing into some object (possibly at some non-zero offset),
`__CPROVER_object_from(ptr)` specifies that the range of bytes starting at `ptr`
and of size `__CPROVER_OBJECT_SIZE(ptr) - __CPROVER_POINTER_OFFSET(ptr)` is assignable.

Revisiting our previous example, changing the target to
`__CPROVER_object_from(vec->data)` still rejects the assignment to `vec->size`,
but allows the assignment to the hidden byte which is located after the data
array in memory.

```c
#include <stdlib.h>

#define MAX_SIZE 10

struct vec_t {
  size_t size;
  char *data;
};

// Allocates a vect_t struct together with its data and a hidden byte
// in a same object.
struct vec_t *vec_alloc(size_t size) {

  if(size > MAX_SIZE)
    size = MAX_SIZE;

  // allocate the struct + data + 1 extra hidden byte
  struct vec_t *vec = malloc(sizeof(struct vec_t) + size + 1);
  if (vec) {
    vec->size = size;
    vec->data = ((char *)vec) + sizeof(struct vec_t);
  }
  return vec;
}

// Clear the vec->data array
void vec_clear(struct vec_t *vec)
  __CPROVER_assigns(
    vec && vec->data: __CPROVER_object_from(vec->data))
{
  if (!vec)
    return;

  vec->size = vec->size; // FAILURE

  for (size_t i = 0; i < vec->size; i++)
    vec->data[i] = 0; // SUCCESS

  char *hidden_byte = ((char *)vec + sizeof(*vec) + vec->size);
  *hidden_byte = 0; // SUCCESS
}

// Proof harness
int main() {
  size_t size;
  struct vec_t *vec = vec_alloc(size);
  vec_clear(vec);
}
```
---

```c
void __CPROVER_object_whole(void *ptr);
```

Given a pointer `ptr` pointing into some object (possibly at some non-zero offset),
`__CPROVER_object_whole(ptr)` specifies that the range of bytes of size
`__CPROVER_OBJECT_SIZE(ptr)` starting at address
`ptr - __CPROVER_POINTER_OFFSET(ptr)` is assignable:

If the pointer has a positive offset into some object, the range includes
bytes that are in the object before the address pointed to by `ptr`.
Revisiting our example one last time, changing the target to
`__CPROVER_object_whole(vec->data)` allows the function (perhaps mistakenly)
to assign to `vec->size`, the whole array of size `vec->size` pointed to by
`vec->data` and the hidden byte.

```c
#include <stdlib.h>

#define MAX_SIZE 10

struct vec_t {
  size_t size;
  char *data;
};

// Allocates a vect_t struct together with its data and a hidden byte
// in a same object.
struct vec_t *vec_alloc(size_t size) {

  if(size > MAX_SIZE)
    size = MAX_SIZE;

  // allocate the struct + data + 1 extra hidden byte
  struct vec_t *vec = malloc(sizeof(struct vec_t) + size + 1);
  if (vec) {
    vec->size = size;
    vec->data = ((char *)vec) + sizeof(struct vec_t);
  }
  return vec;
}

// Clear the vec->data array
void vec_clear(struct vec_t *vec)
  __CPROVER_assigns(
    vec && vec->data: __CPROVER_object_whole(vec->data))
{
  if (!vec)
    return;

  vec->size = vec->size; // SUCCESS

  for (size_t i = 0; i < vec->size; i++)
    vec->data[i] = 0; // SUCCESS

  char *hidden_byte = ((char *)vec + sizeof(*vec) + vec->size);
  *hidden_byte = 0; // SUCCESS
}

// Proof harness
int main() {
  size_t size;
  struct vec_t *vec = vec_alloc(size);
  vec_clear(vec);
}
```
### Function parameters

For a function contract, the memory locations storing function parameters are
considered as being local to the function and are hence always assignable.

For a loop contract, the parameters of the enclosing function are not considered
local to the loop and must be explicitly added to the loop to become assignable.
### Inductive data structures
Inductive data structures are not supported yet in assigns clauses.

## Semantics

Each target listed in an assigns clause defines a
_conditionally assignable range_ of bytes represented by the following triple:

```c
struct {
  void *start_address;
  size_t size;
  bool is_writable;
}
```

where:
- `start_address` is the start address of the range of bytes,
- `size` is the size of the range in number of bytes,
- `is_writable` is true iff the target's `condition` holds and
  `__CPROVER_w_ok(start_address, size)` holds at the program location
  where the clause is interpreted: right before function invocation for
  function contracts and at loop entry for loops;

For contract enforcement, assigns clause targets are turned into checks,
to verify that the function only assigns locations allowed by the assigns clause.

For contract replacement, assigns clause targets are turned into havoc statements,
to model the non-deterministic behaviour specified by the contract.
### Contract Enforcement

In order to determine whether a function (or loop) complies with the _assigns_
clause of the contract, the body of the function (or loop) is instrumented with
assertion statements before each statement which may write to memory (e.g., an
assignment). These assertions check that  the location about to be assigned to
is among the targets specified by the _assigns_ clauses.

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

Assignable locations for the `sum` function are the locations specified with
`__CPROVER_assigns`, together with any location storing a function parameter,
or any location that is locally stack- or heap-allocated as part of function (or loop)
execution.

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

### Contract Replacement

Assuming the _assigns_ clause of the contract correctly captures the set of
locations assigned to by a function (checked during _contract enforcement_),
CBMC will use the contract's [Requires \& Ensures Clauses](../../contracts/requires-and-ensures/#replacement),
and its _assigns clause_ to generate a sound abstraction of the function behaviour from the contract.

Given the contract:

```c
int f(params)
__CPROVER_requires(R);
__CPROVER_assigns(A);
__CPROVER_ensures(E);
{ ... }
```

Function calls `f(args)` get replaced with a sequence of instuctions equivalent to:

```c
// check preconditions
__CPROVER_assert(R[args/params], "Check f preconditions");

// havoc the assignable targets
// for each target t1, t2, ... of A[args/params];
t1 = nondet();
t2 = nondet();
...
// assume post conditions
__CPROVER_assume(E[args/params]);
```
Where `R[args/params]`, `A[args/params]`, `E[args/params]` denote the contract
clause expressions rewritten by substituting
function parameters with the argyments passed at the call site.

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
