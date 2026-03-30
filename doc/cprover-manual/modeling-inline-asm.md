[CPROVER Manual TOC](../../)

## Modeling Inline Assembly

CBMC supports GCC-style (`asm`/`__asm__`) and MSVC-style (`__asm {}`)
inline assembly syntax. During verification, the `remove_asm` pass
translates recognized instructions into equivalent goto-program
operations.

**If an inline-assembly statement contains any unrecognized instruction, the
entire statement is replaced with `skip` — including any sibling instructions
in the same statement that would otherwise be translated.** For example, an
asm statement containing both an `mfence` and an `addl` loses *both*. This may
lead to unsound results if the assembly has side effects that matter for the
property being verified.

### Supported Instructions

#### x86

| Instruction | Effect in CBMC |
|---|---|
| `mfence` | Full memory fence |
| `lfence` | Full memory fence (currently modeled identically to `mfence`) |
| `sfence` | Full memory fence (currently modeled identically to `mfence`) |
| `fstcw` / `fnstcw` | Store FP control word (maps to `__CPROVER_rounding_mode`) |
| `fldcw` | Load FP control word (maps to `__CPROVER_rounding_mode`) |
| `lock` prefix | Only effective when followed by another recognized instruction (e.g. `lock; mfence`); the recognized instruction is wrapped in an atomic section with a full fence. The read-modify-write/exchange value itself is not modeled. |
| `xchg` / `xchgl` | Not modeled: the inline-assembly statement is dropped (treated as unrecognized). |

#### ARM

| Instruction | Effect in CBMC |
|---|---|
| `dmb` | Data memory barrier (full fence) |
| `dsb` | Data synchronization barrier (full fence) |
| `isb` | Empty fence; no observable effect unless combined with a branch |

#### Power

| Instruction | Effect in CBMC |
|---|---|
| `sync` | Full memory barrier |
| `lwsync` | Lightweight sync (all fences except write-after-read) |
| `isync` | Empty fence; no observable effect unless combined with a branch |

### Operand Handling

For GCC extended assembly, CBMC parses the output (`=r`, `+r`) and input
(`r`, `m`) operand lists, but in most cases the operand list does not
influence the generated goto program. For recognized fence instructions (for
example `mfence`, `lfence`, `sfence`, `dmb`, `dsb`, `sync`), the inline
assembly is replaced by a fence and the C-level output operands are not
written. For unrecognized instructions, the entire statement is replaced with
`skip`; output operands are **not** assigned nondeterministic values. Output
operands are only written when the modeled helper for a particular instruction
reads or writes through a pointer associated with that operand — currently
only `fstcw` / `fnstcw` / `fldcw`, which read or write `__CPROVER_rounding_mode`.
Clobber lists are parsed but do not affect verification.

### Limitations

- Only the instructions listed above are modeled. Any inline-assembly
  statement that contains an unrecognized instruction is replaced with `skip`
  in its entirety, **including any recognized instructions in the same
  statement**. This can be unsound if the dropped assembly has side effects
  relevant to the property being verified.
- No diagnostic is emitted for dropped assembly. Use
  `goto-instrument --show-goto-functions` (or `cbmc --show-goto-functions`) to
  inspect whether an inline-assembly statement was translated or dropped.
- For GCC-style inline assembly, complex atomic operations beyond the basic
  `lock; <recognized instruction>` pattern listed above are not modeled as
  single atomic operations; in particular `xchg` and `lock`-prefixed
  read-modify-write instructions (e.g. `lock addl`, `lock cmpxchgl`) are
  dropped.
- MSVC-style `__asm` blocks are parsed, but only the x86
  `mfence` / `lfence` / `sfence`, `fstcw` / `fnstcw`, and `fldcw` instructions
  are modeled. ARM and Power instructions and `lock` / `xchg` patterns are
  **not** modeled for MSVC-style inline assembly.
