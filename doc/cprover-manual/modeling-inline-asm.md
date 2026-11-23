[CPROVER Manual TOC](../../)

## Modeling Inline Assembly

CBMC supports GCC-style (`asm`/`__asm__`) and MSVC-style (`__asm {}`)
inline assembly syntax. Before verification, the `remove_asm` pass replaces
each inline-assembly statement by goto-program instructions:

- On x86 (`--arch i386` or `--arch x86_64`) and AArch64 (`--arch arm64`),
  the default being the host architecture, a GCC-style statement is
  **interpreted** if CBMC's instruction semantics for the architecture
  support all of its instructions (see "x86 Instruction Semantics" and
  "AArch64 Instruction Semantics" below): it is translated into goto-program
  instructions with the same effect on the C program state.
- Otherwise, if CBMC models every instruction of the statement (see
  "Supported Instructions" below, on any architecture), the statement is
  translated into the corresponding fences or calls to library functions.
- Otherwise the statement is **approximated conservatively**: everything the
  statement may change, as far as CBMC can tell from its operands, is
  assigned a nondeterministic value, and a warning that says why the
  statement is not modeled is printed. The modeled instructions of such a
  statement are not translated either.

None of the instructions in the tables below jumps, so an `asm goto`
statement whose instructions are all listed there continues with the next
statement. An interpreted `asm goto` statement jumps to the label that its
instructions jump to.

A statement with an empty assembly template, such as the compiler barrier
`asm volatile("" ::: "memory")`, does nothing.

### x86 Instruction Semantics

The x86 semantics cover the instructions that kernel and library code
commonly uses in inline assembly, with AT&T syntax:

- data movement: `mov`, `movabs`, `movzx`/`movz*`, `movsx`/`movs*`, `lea`,
  `xchg`, `bswap`, `cmov<cc>`, `set<cc>`, sign extensions of the accumulator
  (`cltq`, `cwtl`, `cltd`, `cqto`, ...);
- arithmetic and logic, with the flags they set: `add`, `adc`, `sub`, `sbb`,
  `and`, `or`, `xor`, `not`, `neg`, `inc`, `dec`, `cmp`, `test`;
- shifts and rotates (`shl`, `sal`, `shr`, `sar`, `rol`, `ror`), bit tests
  (`bt`, `bts`, `btr`, `btc`), and bit scans and counts (`bsf`, `bsr`,
  `tzcnt`, `lzcnt`, `popcnt`);
- atomics: the `lock` prefix, `xchg` with a memory operand, `xadd`,
  `cmpxchg`;
- control flow within the statement: `jmp`, `j<cc>` to local and C labels
  (`asm goto`), and flag outputs (`=@cc<cc>`);
- fences (`mfence`, `lfence`, `sfence`), the x87 control word (`fstcw`,
  `fnstcw`, `fldcw`), and instructions without effect on the C program state
  (`nop`, `pause`, `cli`, `sti`, `hlt`, `wrmsr`); `cpuid`, `rdtsc`,
  `rdtscp`, `rdmsr`, and `in` produce nondeterministic values.

Operands follow GCC's rules: inputs are evaluated before the first
instruction (and are subject to the checks CBMC performs), register outputs
are assigned after the last instruction, and memory operands are accessed in
place. Values that the architecture leaves undefined (such as some flags, or
the destination of `bsf` with a zero source) are nondeterministic. The
checks for undefined behaviour of C (such as `--signed-overflow-check`) do
not apply to the instructions, which have defined results on the hardware;
the checks of memory accesses do.

A statement is not interpreted (and hence approximated, unless all of its
instructions are listed in the tables below) if it:

- contains an instruction, operand, prefix, or directive that the semantics
  do not support, or instructions in another section (such as exception
  fixups, which run when an instruction faults); data in other sections (such
  as the Linux kernel's jump tables) is ignored;
- writes a register that is neither bound to an operand nor clobbered: as
  CBMC does not track register variables (`register long x asm("rax")`),
  such a write may change a C variable;
- accesses memory at an address that may be computed from a value that CBMC
  does not model, such as a register that the statement does not initialise
  (which may hold a register variable) or a value that is nondeterministic
  (such as one produced by `rdtsc`): CBMC could not tell which object the
  access changes.

A lock-prefixed instruction (or `xchg` with a memory operand) is an atomic
section with a full fence; the other instructions of the statement are not
part of that atomic section.

### AArch64 Instruction Semantics

The AArch64 semantics cover:

- data movement and processing on general-purpose registers, with the
  condition flags: `mov`, `mvn`, `movz`, `movk`, `movn`, `neg`, `negs`,
  `add`, `adds`, `sub`, `subs`, `and`, `ands`, `orr`, `eor`, `bic`, `bics`,
  `orn`, `eon`, `lsl`, `lsr`, `asr`, `ror`, `cmp`, `cmn`, `tst`, and the
  conditional selects (`csel`, `csinc`, `csinv`, `csneg`, `cset`, `csetm`);
- loads and stores of single registers (including acquire/release
  variants), the LSE atomics
  (`ldadd`, `ldclr`, `ldeor`, `ldset`, `ldsmax`, `ldsmin`, `ldumax`,
  `ldumin`, their `st` forms, `swp`, `cas`), and load-exclusive/
  store-exclusive (`ldxr`, `ldaxr`, `stxr`, `stlxr`, `clrex`);
- branches within the statement and to the labels of `asm goto`, and flag
  outputs (`=@cc<cc>`);
- barriers (`dmb`, `dsb`, `isb`), `mrs` and `msr` of the flags (`nzcv`),
  `msr` of the interrupt masks (`daif`, `daifset`, `daifclr`), and hints
  (`nop`, `yield`, `wfe`, ...); `mrs` of other system registers produces a
  nondeterministic value, and `msr` of other system registers (such as
  `fpcr`, which sets the rounding mode) is not modeled.

A load-exclusive followed by a store-exclusive in the same statement, with
no other memory access, branch, or label in between, is an atomic section.
The store-exclusive succeeds or fails nondeterministically, as the
architecture permits spurious failures, and so does a store-exclusive
without a preceding load-exclusive in the statement (a load-exclusive may
have executed before). Hence symbolic execution needs an unwinding bound for
the loop that retries the sequence until the store succeeds, and unwinding
assertions for that loop fail. If the retried code has no effect when the
store fails (it only computes registers that the next attempt computes
again), the executions with more retries reach the same states, so that
bounding the loop (with `--unwindset`, without unwinding assertions) does not
miss any state.

### Supported Instructions

#### x86

| Instruction | Effect in CBMC |
|---|---|
| `mfence` | Full memory fence |
| `lfence` | Full memory fence (currently modeled identically to `mfence`) |
| `sfence` | Full memory fence (currently modeled identically to `mfence`) |
| `fstcw` / `fnstcw` | Stores the rounding mode (`__CPROVER_rounding_mode`) to bits 10 and 11 of the operand; the other bits of the control word are zero |
| `fldcw` | Sets the rounding mode from bits 10 and 11 of the operand |
| `stmxcsr` | Stores the rounding mode to bits 13 and 14 of the operand; the other bits of the SSE control and status register are nondeterministic |
| `ldmxcsr` | Sets the rounding mode from bits 13 and 14 of the operand |
| `nop`, `pause` | No effect |

For GCC-style statements, the operand of `fstcw`, `fnstcw`, `fldcw`,
`stmxcsr`, and `ldmxcsr` must be an operand reference (`%0`, `%1`, ...); for
MSVC-style blocks, it must be the name of a variable. None of the
read-modify-write instructions that take a `lock` prefix is modeled, and
neither is `xchg`, so statements using them are approximated.

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

Only the x86 fences, `fstcw`, `fnstcw`, `fldcw`, `stmxcsr`, `ldmxcsr`,
`nop`, and `pause` are modeled in MSVC-style blocks.

### Conservative Approximation

The operands of a GCC-style statement are evaluated before the statement,
including any side effects they have. If the statement contains an
instruction that is not modeled, then

1. the input operands (and the in-out operands, those with a `+`
   constraint) are read, which makes them subject to the checks that CBMC
   performs, for example `--pointer-check`;
2. the objects that the input and in-out operands point to, and all objects
   reachable from these, are assigned nondeterministic values. This includes
   operands of pointer type, arrays (which decay to pointers), pointers cast
   to integer types (as in `(uintptr_t)&x`), and the pointer members of
   operands of struct or union type;
3. if the statement has a `"memory"` clobber, or no operands and no clobbers
   at all (basic assembly), all objects of static lifetime, all local
   variables whose address is taken of all functions on the call stack, and
   all objects reachable from these are assigned nondeterministic values;
4. the output operands are assigned nondeterministic values, at the
   addresses they had before the statement, and an `asm goto` statement
   jumps to any of its labels, or continues with the next statement;
5. the rounding mode is assigned a nondeterministic value.

Symbolic execution computes the reachable objects from the value sets of the
pointers stored in the objects (following pointers transitively), so this
includes, for example, all nodes of a linked list whose head is stored in a
variable of static lifetime. The pointers stored in the objects that are
changed are not made arbitrary: each of them is assigned a nondeterministic
choice among the pointers previously stored in these objects, the addresses
of the reachable objects (of a compatible type), and null. The statement can
thus relink a list, and dereferencing the pointers afterwards remains
precise.

MSVC-style blocks have no operand interface. If a block contains an
instruction that is not modeled, each local variable of the enclosing
function that the block names (all of them, if a name is shadowed) is
treated like an output operand and like an input operand of pointer type,
and the block is treated as having a `"memory"` clobber.

### Limitations

- The approximation only reaches the objects listed above. Objects that the
  statement can reach only through pointers that CBMC does not track (for
  example, addresses computed from integers, or pointers stored in local
  variables of a caller whose address is not taken) keep their values.
- A pointer stored in a changed object takes one of at most 64 of the
  candidate values described above (its own previous value first); a warning
  is printed if there are more candidates. Pointers in unions and in arrays
  of more than 64 elements, or of a size that is not constant, are assigned
  arbitrary values.
- Constant objects are not changed.
- Symbolic execution (`cbmc`) computes the reachable objects most
  precisely. The static analyses use their own pointer analyses: the value
  set analyses (as used by `goto-instrument`) and the reaching definitions and
  dependence graph (as used by `goto-analyzer`) follow pointers using their
  value sets, but do not track the contents of heap objects. The other
  abstract domains of `goto-analyzer` treat the statement as changing all
  variables (constant propagation: all objects of static lifetime and all
  address-taken variables). `--full-slice` does not slice programs that
  contain approximated inline assembly with pointer operands, a `"memory"`
  clobber, or no operands (basic assembly).
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
