# CBMC CI infrastructure

This folder contains implementation and configuration files for
our CI infrastructure on top of Github Actions. Aside from CI,
it also contains packaging and automated release scripts.

The files in this folder correspond to:

* `build-and-test-Xen.yaml` -> Build Xen using CBMC tools.
* `csmith.yaml` -> Run 10 randomly generated CSmith tests per Pull Request.
* `doxygen-check.yaml` -> Build project doxygen documentation per Pull Request.
* `pull-request-check-cpplint.sh` -> Script that's called per Pull Request to execute
  `cpplint` over changes.
* `pull-request-check-clang-format.sh` -> Script that's called per Pull Request
  to execute `clang-format` over changes.
* `pull-request-checks.yaml` -> Configuration file for the Github Actions CI jobs
  for the various platforms.
* `regular-release.yaml` -> Configuration file for performing an automated release
  every time a tag of a specific form (`cbmc-x.y.z`) is pushed.
* `release-packages.yaml` -> Configuration file for performing building of build
  artifacts that are attached to release when it's being made. Invoked when a
  regular release is performed.
