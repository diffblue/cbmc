[CPROVER Manual TOC](../)

This document describes the semantics and usage of memory-related and
pointer-related primitives in CBMC.


## Background


### Memory and pointers in CBMC

When CBMC analyzes a program, by default it uses the architectural parameters of
the platform it is running on. That is, on a 64-bit system, CBMC will treat
pointers as having 64 bits. This can be changed by various options (see section
"C/C++ frontend options" in the output of `cbmc --help`).

Memory is represented in CBMC as a set of objects. Each object represents a
contiguous sequence of bytes and is identified via a numeric object ID. For
example, assuming integers of width 4 and chars of width 1, a global integer
variable would correspond to an object of size 4, and memory allocated via
`malloc(10)` would correspond to an object of size 10.

A pointer then consists of two parts: the upper n bits form the object ID, and
the remaining bits form the offset. The object ID part holds the ID of the
object the pointer is pointing to, and the offset part holds the byte offset
within that object. The offset is signed.<sup>1</sup> The null pointer is the
pointer with object ID 0 and offset 0. CBMC uses 8 bits by default to represent
the object ID. This can be changed via the `--object-bits <n>` option.

There are three primitives which directly operate on the value of a pointer:

- `__CPROVER_size_t __CPROVER_POINTER_OBJECT(const void *p)`
- `__CPROVER_ssize_t __CPROVER_POINTER_OFFSET(const void *p)`
- `_Bool __CPROVER_same_object(const void *p, const void *q)`

The primitive `__CPROVER_POINTER_OBJECT(p)` retrieves the object ID part of a
pointer, and the primitive `__CPROVER_POINTER_OFFSET(p)` retrieves the offset
part of a pointer. The `__CPROVER_same_object(p, q)` primitive simply compares
the object IDs of the two given pointers. That is, it is true if and only if
`__CPROVER_POINTER_OBJECT(p) == __CPROVER_POINTER_OBJECT(q)`. It is always valid
to apply these three primitives to a pointer (i.e., they do not have any special
preconditions).

### Memory Objects

Seeing that pointers consist of an object ID and an offset, it remains to
describe how CBMC assigns object IDs to memory objects (such as local variables
or malloced memory). CBMC deterministically assigns consecutive object IDs to
memory objects as it encounters them. For example:

```C
...
char c;

char *p = &c;         // object ID n
char *q = malloc(10); // object ID n + 1

```

Here the pointers `p` and `q` would contain consecutive IDs in their object ID
parts (as retrieved by `__CPROVER_POINTER_OBJECT()`). Due to the deterministic
assignment of object IDs, bugs that can only be exposed with specific pointer
values cannot be found by CBMC. For example:

```C
char *p = malloc(1); // assume cbmc assigns object ID 0xE to the malloced memory
assert(p != (char *)0x0F00000000000000);
```

CBMC will report verification successful for this code snippet (assuming it
assigns an object ID other than 0x0F to the malloced memory). However, assuming
that `malloc()` could allocate memory at any address, the assertion could fail.

Moreover, CBMC does not reuse object IDs for malloced memory. For example:

```C
char *p = malloc(1);
free(p);
char *q = malloc(1);
assert(p != q);
```

CBMC would report verification successful on this code snippet. However,
assuming that `malloc()` could reuse deallocated addresses, the assertion could
fail.

The memory objects in CBMC are independent of each other. That is, for example,
when incrementing a pointer past the bounds of an object, the pointer will never
point into another memory object (such as could happen when running on a real
machine). To verify that pointers stay within the bounds of their pointees, the
CBMC option `--pointer-overflow-check` can be used.

#### Malloc modelling

CBMC ships a model of `malloc` that seeks to emulate the behaviour of the C
standard library. This model is configurable to suit the assumptions the
software under scrutiny may be making. One common assumption, matched by CBMC's
default configuration, is that dynamic memory allocation always succeeds and
`malloc` never returns a `NULL` pointer. Code making such an assumption will
look as follows:

```C
int *p = malloc(sizeof(int));
*p = 42; // unconditional dereference, no check for p being NULL
```

This extends to the case of `malloc(0)`, and CBMC returns a valid pointer to an
object. The size of that object is zero, implying that any attempt to read from
or write to this object will result in an out-of-bounds access. The ensuing
undefined behaviour can be detected by running CBMC with `--pointer-check`.

In an actual execution, however, memory allocation may fail for a number of
reasons and `malloc` would return a NULL pointer. CBMC's model can, therefore,
also be configured to fail allocating memory when the requested allocation size
is larger than representable under CBMC's object-offset model (as described in
[Memory and pointers in CBMC](#memory-and-pointers-in-cbmc)), or even
non-deterministically fail (for any size). Any such failure can either result in
calls to `malloc` returning `NULL`, or reporting such a call as a failed
property. The following command line options facilitate the above failure
configurations:

|Flag                    |  Check                                            |
|------------------------|---------------------------------------------------|
| `--malloc-fail-null`   |  return NULL when emulating an allocation failure |
| `--malloc-may-fail`    |  non-deterministically fail to allocate           |

Note that the use of `--malloc-may-fail` also requires `--malloc-fail-null`. The
following code example demonstrates the effect of these options:

```C
int error = 0;
int *p = malloc(sizeof(int));
if(p != NULL)
  *p = 42;
else
  error = 1;
```

Under CBMC's default model of `malloc`, the `else` branch is unreachable.
When running CBMC with `--malloc-fail-null --malloc-may-fail`, `p` would
non-deterministically be set to `NULL`, making all branches in the above code
reachable.

These malloc failure options need to be set when the C library model is added to
the program. Typically this is upon invoking CBMC, but if the user has chosen to
do so via \ref goto-instrument (using `goto-instrument --add-library`), then the
malloc failure mode needs to be specified with that `goto-instrument`
invocation, i.e., as an option to `goto-instrument`.

### Uninitialized pointers

In verification tools, uninitialized variables are typically treated as having a
nondeterministic value. Programs can thus be verified on a set of potential
inputs. For example:

```C
int i;
__CPROVER_assume(i < 0);
int result = rectify(i);
assert(result == 0);
```

Here, the value of `i` is nondeterministically chosen from all the possible
integer values, and then constrained to negative values via the assumption.
In CBMC, like uninitialized integers, uninitialized pointers are treated as
having a nondeterministic value. That is, the value of the pointer itself is
nondeterministically chosen, though **no memory is allocated**. Therefore,
pointers should be explicitely initialized to ensure that they are backed by
valid memory.


## Memory Primitives

In this section, we describe further memory primitives of CBMC. Above, we have
already encountered the primitives `__CPROVER_POINTER_OBJECT(p)`,
`__CPROVER_POINTER_OFFSET(p)`, and `__CPROVER_same_object(p, q)`. These
primitives just retrieve the object ID part or offset part of a pointer, or
compare the object ID parts of two pointers. It is always valid to apply these
primitives to a pointer (i.e., they do not have any special preconditions).

In the following, we need the concept of a valid pointer. A pointer is *valid*
if it points to a live memory object. That is, it points to the start or to
somewhere within the sequence of bytes that makes up the memory object.

Conversely, a pointer is invalid if it is null, uninitialized,  points to
deallocated dynamic memory, points to an out-of-scope local variable, or has a
value that does not point to (dynamically, automatically, or statically)
allocated memory, or is out of bounds of the memory object it points to (i.e.,
the memory object identified by `__CPROVER_POINTER_OBJECT(p)`).

The primitives below have unspecified semantics on pointers that are neither
null nor valid. CBMC has an option `--pointer-primitive-check` (see section
[Detecting potential misuses of memory primitives](#detecting-potential-misuses-of-memory-primitives) below)
to check that pointers used in the primitives are either null or valid.


### Retrieving the size of a memory object

The following primitive can be used to retrieve the size of the memory object a
pointer points to:

- `__CPROVER_size_t __CPROVER_OBJECT_SIZE(const void *p)`

If `p` is the null pointer, the primitive returns 0. If `p` is valid, the
primitive returns the size of the memory object the pointer points to.
Otherwise, the semantics is unspecified. In particular, it is valid to apply
this primitive to a pointer that points to within a memory object (i.e., not
necessarily to the start). The result is the same as if the pointer would point
to the start of the memory object (i.e., would have offset 0).


### Checking if a pointer points to dynamic memory

The following primitive can be used to check whether a pointer points to dynamic
(malloced, heap) memory:

- `_Bool __CPROVER_DYNAMIC_OBJECT(const void *p)`

If `p` is the null pointer, the primitive returns false. If `p` is valid, the
primitive returns true if the pointer points to dynamically allocated memory,
and false otherwise. If `p` is neither null nor valid, the semantics is
unspecified. Like `__CPROVER_OBJECT_SIZE()`, it is valid to apply the primitive
to pointers that point to within a memory object.


### Checking if a memory segment has at least a given size

The following two primitives can be used to check whether there is a memory
segment starting at the given pointer and extending for at least the given
number of bytes:

- `_Bool __CPROVER_r_ok(const void *p, size_t size)`
- `_Bool __CPROVER_w_ok(const void *p, size_t size)`

At present, both primitives are equivalent as all memory in CBMC is considered
both readable and writeable. The primitives return true if `p` points to a live
object and the object that `p` points into extends to at least `size` more
bytes. Else, an assertion encompassing the primitive will be reported to fail.

```C
char *p = malloc(10);
assert(__CPROVER_r_ok(p, 10)); // valid
p += 5;
assert(__CPROVER_r_ok(p, 3));  // valid
assert(__CPROVER_r_ok(p, 10)); // fails
```

### Modeling valid memory with `rw_ok` assumptions

A common pattern in verification harnesses is to assume that a pointer argument
points to valid memory, without explicitly calling `malloc`. This is done by
combining `__CPROVER_assume` with `__CPROVER_rw_ok` (or `__CPROVER_r_ok` /
`__CPROVER_w_ok`).

**Important:** This feature only activates when `rw_ok` appears inside
`__CPROVER_assume`. Using `rw_ok` in assertions or other contexts does not
create backing objects. Pointers that are not explicitly assumed valid via
`rw_ok` will still correctly fail pointer checks when dereferenced — the
feature does not suppress any genuine memory-safety errors.

#### Arrays

When the size argument is a compile-time constant (or can be resolved to one
through constant propagation) and is larger than a single element, CBMC creates
a backing array object of the appropriate size. The pointer then behaves like
one returned by `malloc`: array indexing, `memcpy`, `__CPROVER_array_copy`, and
other operations all work correctly.

```C
unsigned int *a;
size_t n = 3;
__CPROVER_assume(__CPROVER_rw_ok(a, n * sizeof(*a)));
// a now behaves like a pointer to an array of 3 unsigned ints
a[0] = 10;
a[1] = 20;
a[2] = 30;
assert(a[0] == 10 && a[1] == 20 && a[2] == 30); // succeeds
```

Run with: `cbmc --pointer-check --no-pointer-primitive-check example.c`

#### Pointer aliases

Pointer aliases created before or after the `rw_ok` assumption work correctly:

```C
unsigned int *a;
unsigned int *b = a;                                // alias before assume
__CPROVER_assume(__CPROVER_rw_ok(a, sizeof(*a)));
unsigned int *c = a;                                // alias after assume
*a = 1;
assert(*b == 1 && *c == 1);                         // succeeds
```

#### Inductive data structures (linked lists, trees)

When `rw_ok` is used on a pointer to a struct that contains pointer members,
CBMC automatically creates a chain of valid objects. Each pointer member in the
struct is nondeterministically set to either NULL or a pointer to a fresh valid
object of the same type. When that fresh object is later dereferenced, its
pointer members are initialized in the same way, creating a lazy chain.

The maximum depth of this chain is bounded by the `--unwind` option: with
`--unwind N`, the chain can have at most N-1 nodes.

```C
struct node {
  int data;
  struct node *next;
};

int list_length(struct node *head) {
  int count = 0;
  struct node *curr = head;
  while(curr != 0) {
    count++;
    curr = curr->next;
  }
  return count;
}

int main() {
  struct node *head;
  __CPROVER_assume(__CPROVER_rw_ok(head, sizeof(*head)));
  __CPROVER_assume(head != 0);

  int len = list_length(head);
  assert(len >= 1);  // succeeds: head is non-null, so at least 1 node
}
```

Run with: `cbmc --pointer-check --no-pointer-primitive-check --unwind 4 example.c`

With `--unwind 4`, the list has at most 3 nodes. Increasing `--unwind` allows
verification of longer lists.

This also works for trees and other recursive data structures:

```C
struct tree_node {
  int value;
  struct tree_node *left;
  struct tree_node *right;
};
```

Using `__CPROVER_assume(__CPROVER_rw_ok(root, sizeof(*root)))` on a
`struct tree_node *root` creates a nondeterministic tree bounded by `--unwind`.

Chained dereferences such as `head->next->data` or `root->left->right` can be
used directly: CBMC lifts the intermediate pointers into temporaries (see
`--no-lift-nested-dereferences`), so a guarded access like
`if(head->next) head->next->data` reads the intermediate pointer once and
verifies.

#### Soundness guarantees

The `rw_ok`-in-assumptions feature is designed to not suppress genuine
memory-safety errors:

- **Only explicit `rw_ok` assumptions create objects.** A nondet pointer that is
  dereferenced without a prior `rw_ok` assumption will still fail all pointer
  checks (`pointer NULL`, `pointer invalid`, etc.). The auto-object mechanism
  does not fire for such pointers.

- **Pointer checks are still performed.** Even with `rw_ok`, CBMC checks that
  each dereference is within the bounds of the created object. For example,
  accessing `a[3]` when `rw_ok(a, 3 * sizeof(*a))` was assumed will correctly
  report an out-of-bounds error.

- **NULL is still possible.** For inductive data structures, each pointer member
  is nondeterministically NULL or valid. CBMC explores both possibilities. If
  the code dereferences a pointer without checking for NULL, the NULL case will
  be reported as a failure.

#### Limitations

- **Non-constant sizes:** When the size argument to `rw_ok` cannot be resolved
  to a compile-time constant (e.g., it depends on a nondet variable), the array
  optimization does not apply. The pointer will behave as a single-element
  pointer. Array indexing beyond element 0 may produce incorrect results.

- **Sizes smaller than one element:** When the constant size passed to `rw_ok`
  is smaller than `sizeof(*ptr)`, no backing object can be created. CBMC emits a
  warning and the assumption has no effect; a subsequent dereference will fail
  pointer checks as if no `rw_ok` had been written.

- **Aliases and multi-element `rw_ok`:** For a single-element `rw_ok`
  (`size == sizeof(*ptr)`) the pointer is constrained via an assumption, so an
  alias established *before* the assume (e.g. `b = a;` followed by
  `__CPROVER_assume(__CPROVER_rw_ok(a, sizeof(*a)))`) continues to refer to the
  same object. For a multi-element `rw_ok` the pointer is instead strongly
  assigned to the new array object, so that whole-array operations (such as
  `__CPROVER_array_copy` / `__CPROVER_array_equal`) resolve to a single target;
  this breaks such pre-existing aliases, and `b` keeps its old (nondet) value.

- **Pointer primitive checks:** The `--pointer-primitive-check` option may
  report failures for the `rw_ok` call itself when the pointer is
  uninitialized. Use `--no-pointer-primitive-check` to suppress these when the
  `rw_ok` assumption is intentional.

- **Not a substitute for contracts.** For modular verification with function
  contracts, use `__CPROVER_is_fresh` in `__CPROVER_requires` /
  `__CPROVER_ensures` clauses instead. The `rw_ok`-in-assumptions feature is
  intended for lightweight harness writing without contracts.

#### Comparison with `malloc` and `__CPROVER_is_fresh`

| Feature | `malloc` | `rw_ok` in assume | `is_fresh` in contract |
|---------|----------|-------------------|----------------------|
| Creates backing object | Yes | Yes (constant size) | Yes |
| Array support | Yes | Yes (constant size) | Yes |
| Linked list support | Manual | Automatic (lazy) | Via recursive predicates |
| Pointer aliases | Work | Work | Work |
| Modular verification | No | No | Yes |
| Requires `--no-pointer-primitive-check` | No | Yes | No |

## Detecting potential misuses of memory primitives

As described above, the primitives listed in the Memory Primitives section
require a pointer that is either null or valid to have well-defined semantics.
CBMC has the option `--pointer-primitive-check` to detect potential misuses of
the memory primitives. It checks that the pointers that appear in the following
primitives are either null or valid:

- `__CPROVER_OBJECT_SIZE`
- `__CPROVER_DYNAMIC_OBJECT`
- `__CPROVER_r_ok`
- `__CPROVER_w_ok`

The following three primitives have well-defined semantics even on invalid
pointers. Thus, they have been excluded from the `--pointer-primitive-check`
option.

- `__CPROVER_POINTER_OBJECT`
- `__CPROVER_POINTER_OFFSET`
- `__CPROVER_same_object`

Using them on invalid pointers, however, may still be unintended in user
programs.

<sup>1</sup> Pointers with negative offsets never point to memory objects.
Negative values are used internally to detect pointer underflows.
