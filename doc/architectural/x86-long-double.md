\page x86-long-double Modelling x86 80-bit extended `long double`

\author Michael Tautschnig

# Summary

On x86 hardware, the `long double` C type is the x87 80-bit extended
precision floating-point format, even though it is stored in 12 bytes
(i386) or 16 bytes (x86_64) of memory.  Most other modern targets use
either an IEEE 754 `binary64` (e.g. AArch64 macOS, Windows MSVC) or an
IEEE 754 `binary128` (e.g. AArch64 Linux, ppc64le) layout for `long
double`.  CBMC must model the byte layout of `long double` faithfully
because programs do read `long double` bytes via union-based bit
twiddling -- most prominently the macOS SDK's `<math.h>` inline helpers
for `signbit`, `__inline_isnan`, etc.

This document describes how CBMC encodes the format and where the code
paths live.

# Hardware reference

The 80-bit extended format is documented in:

- Intel® 64 and IA-32 Architectures Software Developer's Manual, vol. 1,
  §4.2.2 ("Floating-Point Data Types").
- The IA-32 ABI for Linux ("System V Application Binary Interface ‒
  i386 Architecture Processor Supplement"), §3.1.2.

The relevant facts are:

- The value occupies 80 bits.  Storage padding extends it to 96 bits on
  i386 (`alignof == 4`) and 128 bits on x86_64 (`alignof == 16`).
- Unlike IEEE binary formats, the leading "integer bit" of the
  significand (the J-bit) is **explicit**: it is stored in the
  encoding, rather than being implicit-1 as in IEEE.
- Exponent width is 15 bits with bias 16383.

The on-disk byte layout, low to high (LSB first):

```
bits   0 ..  62 : explicit fraction (62 bits, no implicit leading 1)
bit       63    : explicit integer bit (J-bit)
bits  64 ..  78 : biased 15-bit exponent
bit       79    : sign bit
bits  80 .. 127 : storage padding (zero on Linux/macOS)
```

For example, on real macOS-15 x86_64 hardware (Xcode 16.4, Apple clang
17.0.0) the 16-byte little-endian dump of `1.0L` is:

```
00 00 00 00 00 00 00 80 ff 3f 00 00 00 00 00 00
```

with bytes 0-7 holding the mantissa `0x8000000000000000` (only the
explicit integer bit set), bytes 8-9 holding the biased exponent
`0x3FFF = 16383`, and bytes 10-15 being storage padding.  Negation flips
bit 79 of the value, giving `... ff bf ...`.

# Modelling

`ieee_float_spect` (in `src/util/ieee_float.h`) records the format:

- `f` -- fraction width (63 for x86 extended).
- `e` -- exponent width (15 for x86 extended).
- `x86_extended` -- when true, the encoding has an explicit integer bit
  at position `f`, so the value width is `f + e + 2` (sign + exponent +
  J-bit + fraction) rather than `f + e + 1`.
- `storage_width_bits` -- when non-zero, the storage container has more
  bits than the value; the high bits are padding zeros.

Three factory methods are provided for the x86 case:

- `ieee_float_spect::x86_80()` -- the bare 80-bit value, used internally
  for solver-internal arithmetic.
- `ieee_float_spect::x86_96()` -- 80-bit value in 96-bit storage (i386
  `long double`).
- `ieee_float_spect::x86_128()` -- 80-bit value in 128-bit storage
  (x86_64 `long double` on Linux, macOS, FreeBSD).

The selection happens in `long_double_type()` (in
`src/util/c_types.cpp`) based on `config.ansi_c.long_double_width` and
`config.ansi_c.arch`.

# Encoding paths

Floating-point values flow through three layers, and each must agree on
the byte layout:

1. **Constants** -- `ieee_float_valuet::pack` / `unpack` in
   `src/util/ieee_float.cpp` produce the `mp_integer` bit pattern that
   the type checker hands off as a constant initialiser.
2. **Expression-level solver** -- `float_bvt` in
   `src/solvers/floatbv/float_bv.cpp` lowers floating-point expressions
   to bit-vector expressions before flattening.
3. **SAT-level solver** -- `float_utilst` in
   `src/solvers/floatbv/float_utils.cpp` produces literals/clauses for
   the SAT back-end directly.

For the x86 extended layout each layer:

- Places the sign bit at `value_width() - 1` (i.e. bit 79), **not** at
  the top of the storage container.
- Places the biased exponent at bits `[f + 1, f + 1 + e)`.
- Places the explicit integer bit at bit `f` (== 63).
- Reads the integer bit out of the encoding rather than synthesising a
  hidden bit during `unpack`.
- Zero-pads the high storage bits during `pack`.

The `boolbvt::convert_rest` handler for `ID_sign` (in
`src/solvers/flattening/boolbv.cpp`) similarly reads the sign from
`value_width() - 1` for `floatbv` operands.

# Why this matters

Before this change, CBMC modelled `long double` on x86_64 as IEEE
`binary128` (`quadruple_precision`).  The two formats agree on the
*value* of representable numbers but disagree on every individual *bit
position*: in `binary128` the sign sits at bit 127, the exponent at
bits 112-126, and there is no explicit integer bit.

The macOS SDK (and similar code in BSD and embedded systems) reaches
into `long double` via a union to extract the sign or classify the
value.  With the binary128 model the `__sexp` field of the SDK's
classification union (bytes 8-9) is always zero, so
`signbit(-1.0L)` evaluates to `0` and dependent control flow never
sees a negative value -- a soundness bug in any analysis that relies
on these classifications.

# Testing

The fix is exercised from three angles:

- `regression/cbmc/long-double-x86-bytes` and
  `regression/cbmc/long-double-i386-bytes` check the byte layout
  against hardware-captured reference bytes.
- `regression/cbmc/long-double-signbit-x86` replicates the macOS SDK
  signbit pattern.
- `regression/cbmc/long-double-roundtrip-x86` exercises
  `double <-> long double` conversion, including the symbolic case.
- `unit/util/ieee_float.cpp` covers the `ieee_float_spect` factories
  and `ieee_float_valuet::pack` / `unpack` against the same hardware
  references.
