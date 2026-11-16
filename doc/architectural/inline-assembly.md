\ingroup module_hidden

\page inline-assembly Inline Assembly

This page describes how `remove_asm` (`src/assembler/`) gives meaning to
inline assembly, and how to extend the instruction semantics. The user-level
description is `doc/cprover-manual/modeling-inline-asm.md`.

## Overview

`remove_asm` replaces every inline assembly statement by goto-program
instructions. Every tool runs it before linking the CPROVER library. For a
GCC-style statement (`code_asm_gcct`), it tries, in this order:

1. the instruction semantics of the configured architecture
   (`config.ansi_c.arch`, see `make_asm_semantics`), if there are any: the
   statement is *interpreted*;
2. the architecture-independent translation of fences, the x87 control word,
   and no-ops (`handle_gcc_command` in `remove_asm.cpp`);
3. the conservative approximation (`asm_approximationt`), with a warning.

MSVC-style blocks use steps 2 and 3 only.

## Interpretation

The interpretation of a statement has these parts:

- `asm_operandst` (`asm_operands.h`) parses the constraints of the operands
  and classifies each operand as a register, memory, immediate, or flag
  output operand. Register inputs that are arrays decay to pointers. The
  symbolic names used in `%[name]` references are kept by the C front end in
  `ID_identifier`.
- `split_asm_template` (`asm_template.h`) splits the template into
  instructions, and resolves `%N`, `%[name]`, `%lN`, and local label
  references.
- `asm_lowering_contextt` (`asm_semantics.h`) holds the goto code being
  built: the storage of register operands, hardware registers, and flags (all
  block-local temporaries), labels, and helpers to read and write registers
  and memory, branch, and fence.
- `asm_semanticst` is the interface of the per-architecture semantics;
  `asm_x86.cpp` implements x86 (i386, x86-64, x32), `asm_aarch64.cpp`
  implements AArch64; `asm_arm_flags.h` has the ARM condition flags.

The code of a statement consists of a prologue that evaluates the inputs, the
code of the instructions, and an epilogue that assigns the register outputs.
Memory operands are accessed in place. A sub-register input is zero-extended
to the register width unless a reference to it reads more bits (see
`asm_semanticst::reference_widens`), in which case the upper bits are
nondeterministic. Zero-extension keeps a constant input constant, which
symbolic execution relies on: otherwise, for example, a spin lock on a lock
word that is written through such an operand would make the lock word
symbolic, and the spin loops would be unwound to the unwinding bound.

The code of the instructions has the checks for undefined behaviour of C
disabled (via pragmas on its source location), as it models hardware
operations whose results are defined. The prologue additionally evaluates the
inputs at the plain source location of the statement, so that the checks
apply to the C expressions of the operands.

The following rules keep the interpretation sound. A statement that violates
one of them is not interpreted:

- Every instruction, prefix, operand form, and directive must be understood.
- Instructions in another section (`.pushsection`/`.section`) are not
  executed in sequence; they may be executed when another instruction faults
  (exception fixups). Data in other sections is ignored.
- A write to a hardware register that is neither bound to an operand by its
  constraint nor clobbered may be a write to a register variable
  (`register long x asm("rax")`), which the front end does not record.
- A memory access must not use an address that may depend on a value that
  is not modeled: a hardware register that the statement does not
  initialise (which may hold a register variable), a nondeterministic value
  (such as a system register, or `rdtsc`), an output operand read before it
  is written, or memory that such a value was stored to. CBMC cannot relate
  such an address to the objects it may point to, so the access would change
  no object. `asm_lowering_contextt::depends_on_unknown` tracks these values
  per position: an unconditional assignment of a known value makes its
  target known; a label joins the states of the fall-through and of the
  forward branches to it; a backward branch must not make a value unknown
  that its target took as known.
- An input tied to a memory output must be the same object.

An instruction that is atomic on the hardware (on x86: lock-prefixed
instructions and `xchg` with a memory operand) is an atomic section of its
own, with a full fence; see `asm_lowering_contextt::mark_atomic`. Making the
whole statement atomic would hide races on the statement's other
instructions.

A load-exclusive followed by a store-exclusive is an atomic section from the
load to the store (`asm_lowering_contextt::begin_exclusive`, `end_exclusive`)
if there is no other memory access, branch, or label in between; otherwise
the statement is not interpreted. The store-exclusive succeeds
nondeterministically: the architecture permits spurious failures, and a
store-exclusive without a load-exclusive in the same statement may succeed if
a load-exclusive executed before. After `clrex` or a store-exclusive, a
store-exclusive fails.

For `asm goto`, goto conversion creates a variable that selects the label to
jump to (`code_asm_gcct::goto_target`) and dispatches on it after the
statement; the interpretation assigns it the index of the label that the
instructions jump to, or 0.

## Adding instructions or an architecture

To add an instruction, extend `lower` of the architecture's
`asm_semanticst`. Return false (via `asm_lowering_contextt::fail`, with a
reason) for any form that is not modeled exactly: the statement is then
approximated, which is always sound. Model values that the architecture
leaves undefined as nondeterministic, not as what one implementation does.

To add an architecture, implement `asm_semanticst` (syntax, register width,
canonical register names, constraint letters, flag conditions, and `lower`)
and return it from `make_asm_semantics`.

Tests that rely on the interpretation must pin the architecture with
`--arch`, as the default is the host architecture. Tests of the
architecture-independent translation and of the approximation use
`--arch riscv64`, which has no instruction semantics and for which CBMC
passes no `-m` option to the host preprocessor. The x86 tests use
preprocessed input (`main.i`), as preprocessing with `-m64` or `-m32` fails
on non-x86 hosts. Expected values of tests of instruction semantics should be
observed on hardware.
