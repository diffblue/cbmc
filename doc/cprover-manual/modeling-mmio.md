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

CBMC uses the built-in function `__CPROVER_allocated_memory(address, size)` to
mark ranges of memory as valid. Accesses within this region are exempt from the
out-of-bounds assertion checking that CBMC would normally do. The function
declares the half-open interval [address, address + size) as valid memory that
can be read and written.

This function can be used anywhere in the source code, but is most commonly used
in the verification harness. Note that there is no flow sensitivity or scope
restriction: CBMC considers accesses to memory regions marked as above valid for
read or write access even before the call to the built-in function is
encountered.

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
functions, use
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
