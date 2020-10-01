# CProver regression tests

This folder contains the CProver regression test-suite.

## Notes

* Tests marked as `winbug` are currently known to be failing
  on Windows, but passing on other platforms. The reason for
  this is not known, and it's currently being investigated.
  This was discovered during work done to port CI from travis
  and codebuild to github actions. Worth noting that those tests
  were not being run on Windows before.