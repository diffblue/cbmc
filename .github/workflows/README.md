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

## CI Platforms

We are currently building and testing CBMC under the following configurations:

* `make` * `gcc` * `linux` (ubuntu 20.04)
* `make` * `clang` * `linux` (ubuntu 20.04)
* `cmake` * `gcc` * `linux` (ubuntu 20.04)
* `make` * `clang` * `macos` (10.15)
* `cmake` * `clang` * `macos` (10.15)
* `cmake` * `vs` * `windows` (vs2019)

Aside from the main platform builds for testing, we are also performing
some auxiliary builds that test packaging support to be up-to-date. We
do that for:

* a `docker` image
* an `ubuntu-20.04` package
* an `ubuntu-18.04` package
* a `windows-msi` installer package

Last but not least, we are also performing a coverage statistics collection
job, which builds CBMC with coverage information on, and then runs the tests,
finally uploading the results to [Codecov](https://about.codecov.io) which
then updates pull request with coverage statistics after the job has finished
running.
