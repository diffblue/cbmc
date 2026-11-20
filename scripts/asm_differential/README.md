# Differential testing of the inline-assembly semantics

These scripts generate the `regression/cbmc/asm_{x86,aarch64,arm}` tests and
can be used to extend them. Each test case (in `asm_differential_cases.py`) is
a small C function with one inline assembly statement. The harness compiles
and runs it on several input vectors, on real hardware for x86-64 and with the
[Unicorn](https://www.unicorn-engine.org/) emulator for AArch64 and AArch32
(A32 code), then writes a CBMC regression test whose assertions pin the
observed results.

If CBMC's semantics for any instruction were wrong, or if a statement were
approximated (its outputs assigned nondeterministic values) rather than
interpreted, the generated assertions would no longer hold, so running the
test under CBMC checks the semantics against the real machine.

## Requirements

* an x86-64 host with `gcc` (x86-64 cases, run natively);
* `aarch64-linux-gnu-gcc`, or else `clang` (AArch64 cases);
* `clang` targeting `armv7a-none-eabi` (AArch32 cases);
* Python packages `unicorn` and `pyelftools` for the emulated architectures.

## Use

```sh
python3 -m venv .venv && .venv/bin/pip install unicorn pyelftools
export ASM_DIFF_MAX_VECTORS=3
.venv/bin/python scripts/asm_differential/asm_differential.py x86_64 regression/cbmc/asm_x86
.venv/bin/python scripts/asm_differential/asm_differential.py aarch64 regression/cbmc/asm_aarch64
.venv/bin/python scripts/asm_differential/asm_differential.py arm regression/cbmc/asm_arm
```

The x86 test is written as `main.i` (preprocessed source), as CBMC's
preprocessing for x86 passes `-m64` to the host's compiler, which fails on
hosts of other architectures.

`ASM_DIFF_MAX_VECTORS` caps the number of input vectors per case; the
committed tests use 3. The input vectors are pseudo-random with fixed seeds,
and the output is passed through `clang-format` with the repository's style
when it is available, so regenerating in a checkout reproduces the committed
files.

## Adding a case

Add a `Case` to the relevant list in `asm_differential_cases.py`: the
statement, the C variables it reads and writes (in the order the harness
stores them), and optionally fixed input vectors or a `constrain` callback for
inputs that must satisfy a precondition (for example a shift count below the
width). A case must be deterministic: it must not read uninitialised storage,
a timer, or I/O. Regenerate the test and check that CBMC verifies it (see the
`test.desc` next to it); a failing assertion is a bug in CBMC's semantics or a
statement that CBMC approximates.

The generated tests only cover statements that CBMC interprets exactly.
Properties that the architecture permits to be violated (such as a
store-exclusive that may fail spuriously) belong in the hand-written
`asm_*_corner_cases` tests.
