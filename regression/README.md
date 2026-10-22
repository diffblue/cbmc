# CProver Regression Tests

This folder contains the CProver regression test-suite.

## Tags

### Backend

- `smt-backend`:
  These tests _require_ the SMT backend and do not work with the SAT backend.
  For example, quantified predicates are not fully supported in SAT.
- `broken-smt-backend`:
  These tests are blocked on missing / buggy goto -> SMT translation rules,
  and therefore do not work with any SMT solver.
- `thorough-smt-backend`:
  These tests are too slow to be run in CI with the SMT backend.

### Standard library headers (`cbmc-cpp`)

- `libcxx`:
  These tests need the libc++ headers (`--stdlib libc++`); they are run only
  where libc++ is installed.
- `libstdcxx`:
  These tests pass only with the libstdc++ headers: they check details of
  those headers (internal names, or the header shapes the test was reduced
  from), or with libc++ or the MSVC STL they fail for a known bug, named in
  the desc (with its KNOWNBUG where it could be reduced).
  `regression/cbmc-cpp`'s CMake and Makefile exclude them, and the
  `libstdcxxNN` tags, when cbmc does not preprocess with GNU gcc: with
  MSVC, or where `gcc` is clang (macOS).
- `libstdcxx12`, `libstdcxx16`:
  These tests need the libstdc++ headers of GCC 12 (resp. GCC 16) or later.
  cbmc preprocesses with the host `gcc`, so `regression/cbmc-cpp`'s CMake and
  Makefile exclude the tags whose version the host `gcc -dumpversion` does not
  meet (`-X libstdcxx16`): with older headers the test would not exercise the
  header shape it was written for.  A test for such a shape belongs here as
  `CORE gcc-only libstdcxx16`, not as KNOWNBUG.
- `broken-libstdcxx16`:
  A CORE test known to fail with the libstdc++ 16 headers; excluded (like
  `libstdcxx16`, by the host `gcc -dumpversion`) when the host gcc is 16 or
  later.  This is temporary: each such test has a KNOWNBUG, reduced to its
  root cause and named in the test's desc, and the tag is removed when that
  KNOWNBUG is fixed.
- `gcc16`:
  Tests motivated by the libstdc++ 16 header shapes; a grouping tag only (the
  test may pass with older headers too).  Combine with `libstdcxx16` when the
  newer headers are required.
- `gnu-extensions`:
  Tests of GNU extensions (`__attribute__`, `__alignof__`, GNU builtins,
  `__complex__`) that both gcc and clang accept; excluded with MSVC.
- `itanium-abi`:
  Tests of class layouts that the Itanium C++ ABI (gcc and clang) defines and
  the MSVC ABI defines differently, such as bit-field allocation; excluded
  with MSVC.
- `gcc-only`:
  Tests that need `goto-cc` in gcc mode (excluded with MSVC or a non-GNU
  build compiler).
- `x86-preprocessing`:
  Tests that preprocess for an x86 target (`--winx64` makes cbmc run
  `gcc -m64`), which GNU gcc for another architecture rejects; excluded on
  such hosts (aarch64 Linux).

### Solver

- `broken-cprover-smt-backend`:
  These tests are known to not work with CPROVER SMT2.
- `thorough-cprover-smt-backend`:
  These tests are too slow to be run in CI with CPROVER SMT2.
- `broken-z3-smt-backend`:
  These tests are known to not work with Z3 (the version running on our CI).
- `thorough-z3-smt-backend`:
  These tests are too slow to be run in CI with Z3.
