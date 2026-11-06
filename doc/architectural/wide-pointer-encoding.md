# Wide Pointer Encoding

## Overview

The `--wide-pointer-encoding` option extends CBMC's pointer bitvector
representation to include a flat integer address alongside the standard
object/offset encoding. This enables precise modeling of pointer-to-integer
casts, integer-to-pointer casts, pointer comparison, and address reuse
after free.

## Pointer Layout

Standard encoding (64-bit platform):
```
[offset(56) | object(8)] = 64 bits
```

Wide encoding (64-bit platform):
```
[object(64) | offset(64) | address(64)] = 192 bits
```

Each component has the full platform pointer width, removing the
`--object-bits` limitation entirely.

### Why object, offset and address are all retained

The three components are not independent: for a pointer to object `i` at
byte offset `f` the encoding maintains the invariant

```
address == object_base_address[i] + f
```

where `object_base_address[i]` is the (symbolic) base address of object
`i`. Given this invariant it is reasonable to ask whether the object and
offset bits are redundant once the flat address is present. They are
retained deliberately, for two reasons:

- CBMC's memory model is object/offset-based. Dereferencing, bounds and
  pointer checks, and the value-set machinery all index memory by object
  and offset. Recovering `(object, offset)` from the address alone would
  require inverting `object_base_address[i] + f`, which depends on the
  base addresses of *all* objects (only fully known once
  `finish_eager_conversion` has run) and is not even a function under
  address reuse: with `malloc_may_alias` two distinct objects may share
  an address, so the inverse is ambiguous. Carrying object/offset
  explicitly lets the existing dereference logic run unchanged.
- Integer-to-pointer reconstruction deliberately assigns *fresh*
  object/offset variables for a given flat address and resolves the
  choice by refinement (see below). The explicit object/offset bits are
  what make such a reconstructed pointer usable by the standard memory
  model.

So the address is the component used by pointer equality, relational
comparison and pointer/integer casts, while object/offset is the
component used by dereferencing and the rest of the memory model; the
invariant above keeps the two views consistent. The cost is the 3x
wider bitvector.

## What It Fixes

### Issue #881: Object-bits limitation

The standard encoding splits the pointer width between object bits and
offset bits. With the default 8 object bits, only 256 objects can be
tracked, and offsets are limited to 56 bits. The wide encoding gives
each component the full 64 bits.

### Issue #8200: Cast-to-pointer misses error

```c
char *x = "";
char *ptr = (char *)0x55a8a2e6b007;
assert(ptr != x);  // Standard: SUCCESS (wrong). Wide: FAILURE (correct).
```

The wide encoding compares pointers by their flat address, not by
object identity. Two pointers from different objects can have the
same address.

### Issue #8161: Inconsistent pointer comparison

```c
int *n = &m;
if((unsigned long)n >= (unsigned long)(-4095))
    assert(...);  // Standard: inconsistent. Wide: consistent.
```

Pointer-to-integer casts return the flat address, making arithmetic
on pointer-derived integers consistent with plain integer arithmetic.

### Issue #8103: Integer-to-pointer casting

```c
uint64_t addr = constrained_to_be_within(buffer);
uint8_t *p = (void *)addr;
assert(*p == expected);  // Standard: FAILURE (wrong). Wide: SUCCESS (correct).
```

The wide encoding adds address-based dereference dispatch: when a
pointer comes from an integer-to-pointer cast, the dereference reads
from the object whose address range contains the pointer's flat address.

### Issue #2117: Address reuse after free

```c
int *x = malloc(sizeof(int));
free(x);
int *y = malloc(sizeof(int));
if(x == y) assert(0);  // Standard: unreachable. Wide: reachable.
```

The wide encoding allows `malloc` to return the same address after
`free` by relaxing the non-overlapping constraint for dynamic objects
and preventing the simplifier from assuming different dynamic objects
have different addresses.

## Additional Features

### Stack Layout Modeling (`--model-stack-layout`)

When combined with `--wide-pointer-encoding`, this option places stack
variables adjacently with architecture-appropriate growth direction
(downward for x86/ARM, upward for HPPA):

```c
int a, b, c;
assert(&a > &b);              // Stack growth direction
assert(&a - &b == sizeof(b)); // Adjacent placement
char *p = (char *)&a;
p[sizeof(a)] = 42;
assert(*(char *)&b == 42);    // Buffer overflow modeling
```

## Technical Details

### Pointer Equality and Comparison

With the wide encoding, `p == q` compares flat addresses (not object
identity). Relational comparisons (`<`, `>`, `<=`, `>=`) also use
flat addresses, making cross-object comparisons well-defined.

### Pointer-to-Integer Cast (P2I)

Returns the flat address component of the pointer. This is the
byte-level address that the program would see on a real machine.

### Integer-to-Pointer Cast (I2P)

Creates a pointer with fresh object/offset variables. Forward
constraints link the object to the address: `obj == i => base[i] + off == addr`.
Backward constraints are added lazily via a refinement loop in
`dec_solve`: if the SAT model assigns an object inconsistent with
the address range, backward constraints are added and the formula
is re-solved.

### Byte Operations

Byte-extract and byte-update on pointer types operate on the 64-bit
address component only. The object/offset bits are internal encoding
and not byte-visible. Pointer arrays store 64-bit addresses per
element, matching symex's byte-level element size.

### Non-Overlapping Constraints

Objects are ordered by index with a chain constraint:
`base[0] + size[0] <= base[1] <= ...` (O(n) instead of O(n²)).
For consecutive dynamic objects of the same size, address reuse is
allowed: `base[next] == base[prev] OR base[next] >= end[prev]`.

### Performance

The wide encoding creates 3× wider pointer bitvectors, increasing
the SAT formula size. Typical overhead is 1.5× on the regression
suite. Programs with many integer-to-pointer casts may be slower
due to the backward constraint refinement.

## Command-Line Options

- `--wide-pointer-encoding`: Enable the wide pointer encoding.
- `--model-stack-layout`: Place stack variables adjacently with
  architecture-appropriate growth direction (requires
  `--wide-pointer-encoding`).
