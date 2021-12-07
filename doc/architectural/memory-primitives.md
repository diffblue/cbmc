\ingroup module_hidden 
\page memory-primitives Memory Primitives

This document describes the semantics and usage of memory-related and
pointer-related primitives in CBMC.


# Background


## Memory and pointers in CBMC

When CBMC analyzes a program, by default it uses the architectural parameters of
the platform it is running on. That is, on a 64-bit system, CBMC will treat
pointers as having 64 bits. This can be changed by various options (see section
"C/C++ frontend options" in the output of `cbmc --help`).

Memory is represented in CBMC as a set of objects. Each object represents a
contiguous sequence of bytes and is identified via a numeric object ID. For
example, assuming integers of width 4 and chars of with 1, a global integer
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

## Memory Objects

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

## Uninitialized pointers

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


# Memory Primitives

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


## Retrieving the size of a memory object

The following primitive can be used to retrieve the size of the memory object a
pointer points to:

- `__CPROVER_size_t __CPROVER_OBJECT_SIZE(const void *p)`

If `p` is the null pointer, the primitive returns 0. If `p` is valid, the
primitive returns the size of the memory object the pointer points to.
Otherwise, the semantics is unspecified. In particular, it is valid to apply
this primitive to a pointer that points to within a memory object (i.e., not
necessarily to the start). The result is the same as if the pointer would point
to the start of the memory object (i.e., would have offset 0).


## Checking if a pointer points to dynamic memory

The following primitive can be used to check whether a pointer points to dynamic
(malloced, heap) memory:

- `_Bool __CPROVER_DYNAMIC_OBJECT(const void *p)`

If `p` is the null pointer, the primitive returns false. If `p` is valid, the
primitive returns true if the pointer points to dynamically allocated memory,
and false otherwise. If `p` is neither null nor valid, the semantics is
unspecified. Like `__CPROVER_OBJECT_SIZE()`, it is valid to apply the primitive
to pointers that point to within a memory object.


## Checking if a memory segment has at least a given size

The following two primitives can be used to check whether there is a memory
segment starting at the given pointer and extending for at least the given
number of bytes:

- `_Bool __CPROVER_r_ok(const void *p, size_t size)`
- `_Bool __CPROVER_w_ok(const void *p, size_t size)`

At present, both primitives are equivalent as all memory in CBMC is considered
both readable and writeable. If `p` is the null pointer, the primitives return
false. If `p` is valid, the primitives return true if the memory segment
starting at the pointer has at least the given size, and false otherwise. If `p`
is neither null nor valid, the semantics is unspecified. It is valid to apply
the primitive to pointers that point to within a memory object. For example:

```C
char *p = malloc(10);
assert(__CPROVER_r_ok(p, 10)); // valid
p += 5;
assert(__CPROVER_r_ok(p, 3));  // valid
assert(__CPROVER_r_ok(p, 10)); // fails
```

# Detecting potential misuses of memory primitives

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

