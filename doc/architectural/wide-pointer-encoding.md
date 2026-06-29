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

## Technical Details

### Pointer Equality and Comparison

With the wide encoding, `p == q` compares flat addresses (not object
identity). Relational comparisons (`<`, `>`, `<=`, `>=`) also use
flat addresses, making cross-object comparisons well-defined.

### Pointer-to-Integer Cast (P2I)

Returns the flat address component of the pointer. This is the
byte-level address that the program would see on a real machine.

### Integer-to-Pointer Cast (I2P)

I2P reconstruction is the most involved part of the encoding: the result
pointer's object/offset must be recovered from a flat address that the
program may have computed arbitrarily. Three situations funnel into the
same routine, `reconstruct_pointer_from_address()`:

- an integer-to-pointer typecast `(T *)integer`, where the integer bits are
  the flat address;
- a `byte_extract`/`byte_update` producing a pointer-typed result (e.g. a
  pointer read out of a `char` buffer): the platform-width address bytes are
  extracted and the pointer is reconstructed from them (see Byte Operations);
- more generally, any pointer value that arrives as a flat integer address.

#### Reconstruction

Given a flat address `addr`, `reconstruct_pointer_from_address()`:

1. if `addr` is the constant `0`, returns the canonical NULL encoding;
2. otherwise allocates *fresh* object and offset variables `obj`, `off`,
   and constrains a non-zero address to a non-NULL object;
3. records a `pending_i2pt` entry (`obj`, `off`, `addr`, the number of
   objects known at this point, and a cache of the per-object `obj == i`
   literals) for the deferred and lazy constraints below;
4. emits *forward* constraints for every object `i` already known:
   `obj == i  =>  base[i] + off == addr`;
5. freezes `obj`, `off` and `addr` (see Variable Freezing).

The result is `object_offset_encoding(obj, off, addr)`. The flag
`force_base_for_all_objects` controls whether forward constraints are
emitted for *all* objects (integer-to-pointer typecasts, where the address
may name any object) or only for objects that already have a base address
(byte-level reconstruction).

#### Forward vs backward constraints

The forward constraint `obj == i => base[i] + off == addr` only fixes the
offset *given* a chosen object. Because `off` is unconstrained, the solver
could pick *any* object `i` and set `off = addr - base[i]`, yielding an
out-of-bounds offset into an object whose address range does not actually
contain `addr`. Soundness therefore also needs the *backward* direction:

```
base[i] <= addr < base[i] + size[i]   =>   obj == i
```

i.e. an address lying within object `i`'s range must reconstruct to object
`i`. Materialising this for every (pending cast x object) pair is expensive
and usually unnecessary, so it is added **lazily by refinement** in
`check_SAT_backward_i2p()`, driven by the `dec_solve()` loop: after each
satisfiable solve the model is inspected, and if some reconstruction chose
an object inconsistent with the address ranges, the backward constraints
are added and the formula re-solved. Most queries converge without ever
materialising them.

#### Deferral to finish_eager_conversion

Objects are discovered *during* conversion, so when an I2P cast is converted
not all objects exist yet; `objects_at_creation` records how many did. The
forward constraints in step 4 cover only those. `finish_eager_conversion()`,
which runs once the full object set is known, completes each pending
reconstruction by:

- adding the forward constraints for objects created *after* the cast, and
- adding a validity clause requiring `obj` to equal *some* known object (the
  disjunction of all `obj == i`).

### Byte Operations

Byte-extract and byte-update on pointer types operate on the platform-width
address component only; the object/offset bits are internal encoding and not
byte-visible. Pointer arrays store one platform-width address per element,
matching symex's byte-level element size. A byte-extract that yields a
pointer reconstructs it from the extracted address via the I2P routine
above.

### Object Base Addresses and Layout

Each object's flat base address is a fresh symbolic vector
`object_base_address[i]` (`get_object_base_address()`), created and
constrained in `finish_eager_conversion()` so that the flat-address view
stays consistent with the object/offset view:

- the NULL object's base is `0`;
- `base[i] + size[i]` must not wrap around the address space (overflow
  guard);
- base addresses are **aligned** — the low bits are forced to zero up to the
  largest power of two not exceeding the object size (capped at the word
  size). This mirrors the alignment the standard encoding assumes, so
  programs that observe it (e.g. `((size_t)&x & 1) == 0`) behave as in
  standard mode;
- objects are laid out **non-overlapping** by a chain constraint over the
  object order, `base[i] + size[i] <= base[i+1]`, which is O(n) rather than
  the O(n^2) of constraining all pairs.

Objects that are themselves integer-derived addresses
(`integer_address_objects`) are excluded from the non-overlap chain, since
such an address may legitimately fall inside another object.

### Variable Freezing

All fresh variables created for the wide encoding -- the `obj`/`off`/`addr`
of each reconstruction, the per-object base addresses, and everything added
in `finish_eager_conversion()` -- are frozen (`prop.set_frozen`). The
decision procedure runs incrementally (the backward-constraint refinement
re-solves), and MiniSat's simplifier would otherwise be free to eliminate
variables that the later refinement clauses reference, which would trip an
invariant. `finish_eager_var_start` records the variable count at the start
of `finish_eager_conversion()` so exactly the newly created variables are
frozen.

### Performance

The wide encoding creates 3× wider pointer bitvectors, increasing
the SAT formula size. Typical overhead is 1.5× on the regression
suite. Programs with many integer-to-pointer casts may be slower
due to the backward constraint refinement.

## Command-Line Options

- `--wide-pointer-encoding`: Enable the wide pointer encoding.
