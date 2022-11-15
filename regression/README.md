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

### Solver

- `broken-cprover-smt-backend`:
  These tests are known to not work with CPROVER SMT2.
- `thorough-cprover-smt-backend`:
  These tests are too slow to be run in CI with CPROVER SMT2.
- `broken-z3-smt-backend`:
  These tests are known to not work with Z3 (the version running on our CI).
- `thorough-z3-smt-backend`:
  These tests are too slow to be run in CI with Z3.

### Platform

- `winbug`:
  These tests are currently known to be failing on Windows,
  but passing on other platforms.
  The reason for this is not known, and it's currently being investigated.
  This was discovered during work done to port CI from [Travis]
  and [AWS CodeBuild] to [GitHub Actions].
  Worth noting that those tests were not being run on Windows before.


[AWS CodeBuild]: https://aws.amazon.com/codebuild/
[GitHub Actions]: https://github.com/features/actions
[Travis]: https://travis-ci.com/
