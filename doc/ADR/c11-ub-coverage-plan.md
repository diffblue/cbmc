\page c11-ub-coverage-plan Covering C11 Undefined Behaviors in CBMC

This document tracks which C11 undefined behaviors (Appendix J.2) CBMC
does not yet check and categorizes them by feasibility. The reference
list is in `doc/cprover-manual/c11-undefined-behavior.md`. Row numbers below refer
to that table.

## Tier 1 — Front-end / type-checker checks

Small effort each. These are compile-time constraints the C front-end or
linker could reject or warn about.

| Row | J.2 ref | Description | Status |
|-----|---------|-------------|--------|
| 4 | 5.1.2.2.1 | `main()` not in specified form | |
| 8 | 6.2.2 | Same identifier with internal and external linkage | |
| 20 | 6.3.2.1 | Non-array lvalue with incomplete type used where a value is required | |
| 22 | 6.3.2.1 | Array lvalue with `register` storage converted to a pointer | |
| 32 | 6.4.2.2 | Explicit declaration of `__func__` | |
| 38–40 | 6.5.2.2 | Calls without prototype / wrong argument count or types | partially checked |
| 41 | 6.5.2.2 | Function defined with incompatible type | |
| 59 | 6.7 | Object with no linkage and incomplete type | |
| 60 | 6.7.1 | Block-scope function with non-`extern` storage class | |
| 61 | 6.7.2.1 | Struct/union without named members | |
| 63 | 6.7.2.3 | Incomplete struct/union not completed in same scope | |
| 66 | 6.7.3 | Function type with type qualifiers | |
| 67 | 6.7.3 | Qualified types required to be compatible without identical qualification | |
| 70 | 6.7.4 | Inline + external linkage but not defined in TU | |
| 71 | 6.7.4 | `_Noreturn` function returns | |
| 78 | 6.7.6.3 | Storage-class specifier or qualifier on `void` parameter | |
| 84 | 6.9 | Missing/duplicate external definitions | |
| 85–86 | 6.9.1 | K&R function definition issues | |
| 88 | 6.9.1 | `}` reached in non-void function, value used | |
| 89 | 6.9.2 | Internal linkage + incomplete type + tentative def | |

## Tier 2 — Runtime checks (goto-check instrumentation)

Medium effort each. These require adding assertions during the
goto-check pass, similar to existing bounds/pointer/overflow checks.

| Row | J.2 ref | Description | Status |
|-----|---------|-------------|--------|
| 5 | 5.1.2.4 | Data races | CBMC has concurrency support |
| 10 | 6.2.4 | Use of pointer to ended-lifetime object | extend pointer-check |
| 11 | 6.2.4 | Use of indeterminate (uninitialized) value | |
| 12–13 | 6.2.6.1 | Trap representations | |
| 18 | 6.3.1.5 | Float demotion out of range | extend float-overflow-check |
| 21 | 6.3.2.1 | Use of uninitialized `register`-eligible automatic object | extend uninitialized-value check (cf. row 11) |
| 24 | 6.3.2.3 | Pointer-to-integer conversion out of range | extend conversion-check |
| 25 | 6.3.2.3 | Misaligned pointer conversion | |
| 26 | 6.3.2.3 | Function pointer type mismatch on call | extend function-pointer removal |
| 35 | 6.5 | Unsequenced side effects | needs sequence-point analysis |
| 37 | 6.5 | Strict aliasing violation | needs type-based alias analysis |
| 46 | 6.5.6 | Pointer arithmetic producing out-of-bounds result | partially covered |
| 50 | 6.5.6 | Pointer subtraction result not representable in `ptrdiff_t` | |
| 54 | 6.5.16.1 | Assignment to overlapping object | |
| 62 | 6.7.2.1 | Access flexible array member with no elements | extend bounds-check |
| 65 | 6.7.3 | Volatile access through non-volatile lvalue | |
| 68–69 | 6.7.3.1 | `restrict` pointer violations | needs restrict analysis |
| 77 | 6.7.6.3 | `static` array parameter size not met at call site | |
| 136–143 | 7.16 | `va_list` / `va_arg` misuse | |
| 176 | 7.22.3 | Use of zero-size allocation | extend pointer-check |
| 179 | 7.22.3 | Double free / free of non-malloc'd pointer | partially covered |

## Tier 3 — C library model improvements

Small effort each, mostly mechanical: add precondition assertions to
existing library models in `src/ansi-c/library/`.

| Row | J.2 ref | Description | Status |
|-----|---------|-------------|--------|
| 108 | 7.1.4 | Invalid argument to library function | |
| 113 | 7.4 | Character function argument not `EOF`/`unsigned char` | |
| 126–127 | 7.13.2.1 | `longjmp` to nonexistent/modified environment | |
| 146–175 | 7.21 | stdio / file I/O UBs (~30 items) | |
| 153–168 | 7.21.6 | printf/scanf format string UBs (~16 items) | partial printf model exists |
| 178,180–181 | 7.22.3 | `aligned_alloc`/`malloc`/`realloc` allocation UBs (176, 179 are runtime checks, see Tier 2) | |
| 184 | 7.22.4.6 | Modifying `getenv`/`strerror` result | |
| 187–189 | 7.22.5 | `bsearch`/`qsort` invalid arguments | |
| 190 | 7.22.7 | Multibyte conversion state | |
| 193–194 | 7.24.4.5 | `strxfrm`/`strtok` misuse | |
| 197 | 7.27.3.1 | `asctime` out-of-range argument | |

## Tier 4 — Out of scope

These are preprocessor-phase, translation-phase, or environmental issues
that CBMC cannot meaningfully check because it operates on
already-preprocessed code.

Rows: 1–3, 6–7, 14, 16, 28–31, 34, 42, 72–74, 76, 79–80, 90–99,
101–107, 110–112, 114–118, 120–125, 128–135, 144–145, 182–183,
185–186, 195–196, 198–203.

~70 items. Not planned.

## Recommended priorities

1. **Quick wins**: [71] `_Noreturn` returns and [88] non-void function
   fall-through — common bugs, easy to add as goto-check assertions.

2. **High value**: [11] indeterminate values, [25] misaligned pointers,
   [50] `ptrdiff_t` overflow, [77] `static` array parameter size —
   catch real bugs users care about.

3. **Library models**: printf/scanf format checking [153–168] covers 16
   UBs at once. stdio state tracking [146–175] is another large cluster.

4. **Long-term**: [5] data races, [35] sequence points, [37] strict
   aliasing, [68–69] `restrict` — architecturally hard but high value.
