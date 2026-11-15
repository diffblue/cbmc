[CPROVER Manual TOC](../../)

## Modeling Inline Assembly

CBMC supports GCC-style (`asm`/`__asm__`) and MSVC-style (`__asm {}`)
inline assembly syntax. Before verification, the `remove_asm` pass replaces
each inline-assembly statement by goto-program instructions:

- If CBMC models every instruction of the statement (see the tables below),
  the statement is translated into the corresponding fences or calls to
  library functions.
- Otherwise the statement is **approximated conservatively**: everything the
  statement may change, as far as CBMC can tell from its operands, is
  assigned a nondeterministic value, and a warning that names the first
  instruction that is not modeled is printed. The modeled instructions of
  such a statement are not translated either.

A statement with an empty assembly template, such as the compiler barrier
`asm volatile("" ::: "memory")`, does nothing.

### Supported Instructions

#### x86

| Instruction | Effect in CBMC |
|---|---|
| `mfence` | Full memory fence |
| `lfence` | Full memory fence (currently modeled identically to `mfence`) |
| `sfence` | Full memory fence (currently modeled identically to `mfence`) |
| `fstcw` / `fnstcw` | Stores the rounding mode (`__CPROVER_rounding_mode`) to bits 10 and 11 of the operand; the other bits of the control word are zero |
| `fldcw` | Sets the rounding mode from bits 10 and 11 of the operand |
| `nop`, `pause` | No effect |

For GCC-style statements, the operand of `fstcw`, `fnstcw`, and `fldcw` must
be an operand reference (`%0`, `%1`, ...); for MSVC-style blocks, it must be
the name of a variable. None of the read-modify-write instructions that
take a `lock` prefix is modeled, and neither is `xchg`, so statements using
them are approximated.

#### ARM

| Instruction | Effect in CBMC |
|---|---|
| `dmb`, `dsb` | Full fence without an option or with option `sy`, `ish`, `osh`, or `nsh`; with an option ending in `ld` (such as `ishld`), loads are ordered before later loads and stores; with an option ending in `st` (such as `ishst`), stores are ordered before later stores |
| `isb` | Empty fence; no observable effect unless combined with a branch |
| `nop`, `yield` | No effect |

#### Power

| Instruction | Effect in CBMC |
|---|---|
| `sync`, `hwsync` | Full memory barrier |
| `lwsync` | Lightweight sync (all fences except write-after-read) |
| `eieio` | Orders stores before later stores |
| `isync` | Empty fence; no observable effect unless combined with a branch |
| `nop` | No effect |

Only the x86 fences, `fstcw`, `fnstcw`, `fldcw`, `nop`, and `pause` are
modeled in MSVC-style blocks.

### Conservative Approximation

The operands of a GCC-style statement are evaluated before the statement,
including any side effects they have. If the statement contains an
instruction that is not modeled, then

1. the input operands (and the in-out operands, those with a `+`
   constraint) are read, which makes them subject to the checks that CBMC
   performs, for example `--pointer-check`;
2. the objects that the input and in-out operands point to are assigned
   nondeterministic values. This includes operands of pointer type, arrays
   (which decay to pointers), pointers cast to integer types (as in
   `(uintptr_t)&x`), and the pointer members of operands of struct or union
   type;
3. if the statement has a `"memory"` clobber, or no operands and no clobbers
   at all (basic assembly), all objects of static lifetime, the objects that
   those of them that are pointers (or structs or unions with pointer
   members) point to, and all local variables of the enclosing function whose
   address is taken are assigned nondeterministic values;
4. the output operands are assigned nondeterministic values, at the
   addresses they had before the statement;
5. the rounding mode is assigned a nondeterministic value.

MSVC-style blocks have no operand interface. If a block contains an
instruction that is not modeled, each local variable of the enclosing
function that the block names (all of them, if a name is shadowed) is
treated like an output operand and like an input operand of pointer type,
and the block is treated as having a `"memory"` clobber.

### Limitations

- The approximation only reaches the objects listed above. Objects that the
  statement can reach only through other pointers, for example heap objects
  or local variables of a caller that are not pointed to by an operand or an
  object of static lifetime, keep their values. Objects of static lifetime
  that are added when linking the CPROVER library are not changed.
- Constant objects and the objects that pointers to constant types point to
  are not changed.
- Control flow out of a statement is not modeled: `asm goto` statements
  always continue with the next statement.
- Atomicity and memory ordering of instructions that are not modeled are not
  modeled; such statements are not atomic and do not act as fences.
- A loop that retries an approximated statement until it succeeds, such as a
  spin lock that is acquired with `xchg` or `cmpxchg`, may retry arbitrarily
  often, as the result of each attempt is nondeterministic. Symbolic
  execution thus unwinds such loops up to the unwinding bound, and their
  unwinding assertions fail. Replace the functions that contain such loops
  by C models (for example, with `goto-instrument --remove-function-body`
  and a definition of the function without inline assembly).
- CBMC does not check whether the instructions are valid for the target
  architecture: for example, `sync` is modeled as a Power barrier regardless
  of the `--arch` option.
- You can use `goto-instrument --show-goto-functions` (or
  `cbmc --show-goto-functions`) to inspect how an inline-assembly statement
  was translated.
