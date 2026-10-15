[CPROVER Manual TOC](../../)

## Modeling Memory-mapped I/O

Input and output between CPU and devices is facilitated using
[port-mapped or memory-mapped I/O](https://en.wikipedia.org/wiki/Memory-mapped_I/O).
The former uses dedicated instructions, while the latter uses read or write
access to specific locations in memory.
In absence of any further modeling, CBMC would consider such accesses
out-of-bounds (cf. [program properties](../../properties/)).
Furthermore, reads or writes to these specific memory locations may result in
the device exhibiting some behavior.
Both situations require modeling to ensure that CBMC can perform verification
that is faithful to the behavior exhibited in concrete execution.

### Declaring memory mapping

When low-level code uses memory-mapped I/O to access a device, registers of the
device are mapped to specific locations in memory. Code reads or writes a
register in the device by reading or writing a specific location in memory. For
example, if the second bit in a configuration register is to be set, and if that
configuration register is mapped to the byte at location 0x1000 in memory, then
code sets the second bit of the byte at 0x1000. The problem posed by
memory-mapped I/O is that there is no declaration or allocation in the source
code specifying this location 0x1000 as a valid region of memory. Nevertheless
accesses within this region are valid memory accesses, and should not be flagged
as an out-of-bounds memory reference. This is an example of
implementation-defined behavior that must be modeled to avoid reporting false
positives.

CBMC provides two mechanisms for declaring memory-mapped I/O regions:

1. **`--mmio-region address:size` (recommended):** Declare regions on the
   command line. Each region becomes a byte-array object in the symbol table.
   Reads and writes to addresses within a declared region are redirected to the
   corresponding array element. See the
   [per-region object model](#per-region-object-model-recommended) section below.

2. **`__CPROVER_allocated_memory(address, size)` (deprecated):** A built-in
   function that marks the half-open interval [address, address + size) as valid
   memory. Accesses within this region are exempt from out-of-bounds assertion
   checking. This function can be used anywhere in the source code, but is most
   commonly used in the verification harness. Note that there is no flow
   sensitivity or scope restriction: CBMC considers accesses to memory regions
   marked as above valid for read or write access even before the call to the
   built-in function is encountered.

> **Deprecation notice:** `__CPROVER_allocated_memory` is deprecated. Use
> `--mmio-region` instead, which provides better scalability and does not
> require source-code changes.

### Device behavior

A memory-mapped I/O region is an interface to a device. Values returned by
reading and writing this region of memory need not follow the semantics of
ordinary read-write memory. Imagine a device that can generate unique
identifiers. If the register returning the unique id is mapped to the byte at
location 0x1000, then reading location 0x1000 will return a different value
every time, even without intervening writes. These side effects have to be
modeled.  One easy approach is to ‘havoc’ the device, meaning that writes are
ignored and reads return non-deterministic values. This is sound, but may lead
to too many false positives. To model the device semantics more precisely, use
one of the options described below.

*If the device has an API,* havoc the device by removing the implementation
using `goto-instrument`'s `--remove-function-body` command-line parameter.
Assume the API is called `device_access`. Using
`goto-instrument --remove-function-body device_access` will drop the
implementation of the function device_access from compiled object code.
If there is no other definition of `device_access`, CBMC will model each
invocation of `device_access` as returning an unconstrained value of the
appropriate return type. Now, to havoc a device with an API that includes a read
and write method, use this command-line option to remove their function bodies,
and CBMC will model each invocation of read as returning an unconstrained value.
At link time, if another object file, such as the test harness, provides a
second definition of `device_access`, CBMC will use this definition in its
place. Thus, to model device semantics more precisely, provide a device model in
the verification harness by providing implementations of (or approximations for)
the methods in the API.

*If the device has no API,* meaning that the code refers directly to the address
in the memory-mapped I/O region for the device without reference to accessor
functions, there are two approaches available.

#### Per-region object model (recommended)

Use `--mmio-region <address>:<size>` to declare each
contiguous MMIO region as an individual object. Each region becomes a byte array
in the symbol table, named `__CPROVER_mmio_region_0x<address>`. Reads and writes
to addresses within a declared region are redirected to the corresponding bytes
of that array. An access wider than a single byte spans the appropriate number
of consecutive bytes (`ceil(width / 8)`), honouring the endianness configured
for the program, so multi-byte loads and stores are modelled faithfully (a
32-bit store updates four bytes rather than truncating to one).

This option is supported by both `cbmc` and `goto-instrument`.

This approach avoids the scalability problems of the single-array callback model:
each write only updates the targeted region object rather than the entire memory
array.

For example, given firmware that accesses a UART at `0x40000000` (256 bytes) and
a GPIO controller at `0x40001000` (64 bytes):

```sh
# Directly with cbmc:
cbmc --mmio-region 0x40000000:256 \
  --mmio-region 0x40001000:64 \
  --no-pointer-check --no-bounds-check firmware.c

# Or via goto-instrument:
goto-cc -o firmware.gb firmware.c
goto-instrument --mmio-region 0x40000000:256 \
  --mmio-region 0x40001000:64 \
  firmware.gb firmware-mod.gb
cbmc --no-pointer-check --no-bounds-check firmware-mod.gb
```

The `--no-pointer-check` and `--no-bounds-check` flags are needed because
integer addresses used for MMIO are not valid pointers from CBMC's perspective.

Constant addresses are resolved at instrumentation time to a byte offset within
the region's array. Symbolic addresses (e.g., a pointer that could refer to
either region) are handled via a conditional dispatch over all declared regions.

Regions must not overlap; both `cbmc` and `goto-instrument` will report an
error if overlapping regions are specified.

Storing and loading C pointer values through an MMIO region is not fully
supported: a pointer written to a region is serialised to its bytes, and
reading it back does not reconstruct the original pointer's object identity.
Such accesses may therefore be modelled imprecisely.

#### Callback model

Alternatively, use
```C
__CPROVER_mm_io_r(address, size)
__CPROVER_mm_io_w(address, size, value)
```
to model the reading or writing of an address at a fixed integer address. If the
test harness provides implementations of these functions, CBMC will use these
functions to model every read or write of memory. For example, defining
```C
char __CPROVER_mm_io_r(void *a, unsigned s) {
  if(a == 0x1000)
    return 2;
  else
    return nondet_char();
}
```
will return the value 2 upon any access at address 0x1000, and return a
non-deterministic value in all other cases.

The callback model can be combined with `--mmio-region`: per-region
instrumentation runs first to give declared regions precise array-backed
modeling, and the callbacks then handle any remaining dereferences. This is
useful when some regions need custom read/write behaviour beyond simple
nondeterministic access.

Note that the callback model uses a single unbounded `__CPROVER_memory` array,
which means every write implies an update of the entire array. For programs with
many MMIO regions, the per-region object model described above is preferred.
