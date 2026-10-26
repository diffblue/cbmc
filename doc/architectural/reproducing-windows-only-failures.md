# Reproducing Windows-only C++ Failures on Linux

Status: method, used in October 2026 to fix the cbmc-cpp tests that failed
only on the Visual Studio CI jobs.  None of the local patches below is in
the tree; this page says how to recreate them.

## Why Windows behaves differently

On Windows, cbmc preprocesses with `cl` (`ansi_c.preprocessor` is
`VISUAL_STUDIO`, see `configt::set` in `src/util/config.cpp`), so a C++
test sees the MSVC STL and the Windows SDK headers, `_MSC_VER` and cl's
predefined macros.  `--64` is LLP64 (`configt::ansi_ct::set_64`), and the C
library models in `src/ansi-c/library` are also preprocessed by cl, with the
SDK's `stdio.h`, `string.h` and so on.  Each of these differs from a Linux
run with `--winx64`, which still preprocesses with gcc and is LP64 for
`--64`.

## Step 1: the CI artifacts

Both Visual Studio jobs (and the macOS jobs) run
`scripts/preprocess_cpp_tests.ps1` (`.sh` on macOS) after the tests, which
preprocesses every failed cbmc-cpp test, and the tests listed in
`env.cpp-preprocess-tests` of `pull-request-checks.yaml`, with the
runner's toolchain.  Download them:

```sh
gh run download <run-id> -n msvc-preprocessed-headers -D /tmp/msvc
gh run download <run-id> -n msvc-2022-preprocessed-headers -D /tmp/msvc22
```

`test_<name>.ii` is the test's source as cl preprocessed it.  Run it with
the test's options plus `--winx64`:

```sh
tr -d '\r' < /tmp/msvc/test_X.ii > X.ii
cbmc --winx64 <options from test.desc> X.ii
```

Two differences remain, and they matter for some tests:

* With gcc as the preprocessor, the C library models are preprocessed with
  the Linux headers for a Windows target, which fails, so the library
  functions have no body.  Tests whose result depends on `memcpy`,
  `memmove`, `memcmp`, `memset` or `strlen` need copies of those models
  pasted before the test's `main` (keeping its `#line` numbering).
* `--64` in a desc still means LP64.

## Step 2: emulating a Windows host

Two small local patches to `src/util/config.cpp`, under an environment
variable (say `CBMC_EMULATE_WINDOWS_HOST`), make a Linux build behave like
a Windows build for these settings:

* in `configt::set`, in the `os == "windows"` branch without `--gcc`, the
  non-`_WIN32` case: set `ansi_c.preprocessor` to `VISUAL_STUDIO` when the
  variable is set (the mode is `VISUAL_STUDIO` already);
* in `configt::ansi_ct::set_64`: call `set_LLP64()` when the variable is
  set.

With the first patch, cbmc invokes `cl`, which does not exist on Linux;
it is needed for the code paths that depend on the preprocessor setting
(for instance which builtins the C++ front end declares, or the
`/Zc:__cplusplus` handling in `c_preprocess.cpp`), and is combined with
Step 3 for the C library.  The `.ii` file from Step 1 is already
preprocessed, so it needs no preprocessor.

## Step 3: replaying the C library preprocessed by cl

To see the C library models as Windows sees them:

1. On CI, dump the input and output of each preprocessing of a text (the
   library models are preprocessed one text at a time by
   `c_preprocess(std::istream &, ...)` in `src/ansi-c/c_preprocess.cpp`):
   with an environment variable `CBMC_DUMP_PREPROCESSED_DIR` set, write the
   temporary file's contents to `<dir>/ppN.in.c` and the preprocessed
   result to `<dir>/ppN.out.c`, numbering the calls.
2. Locally, in the same function: with `CBMC_REPLAY_PREPROCESSED_DIR` set,
   compare the input text with each `ppN.in.c` (after removing `\r` and a
   UTF-8 byte-order mark) and, on a match, return the contents of
   `ppN.out.c` instead of running the preprocessor.

Together with Step 2, a local run then links the same library code as the
Windows run.  This found the failure to link the Windows SDK's inline stdio
functions ("fgetc type inconsistency" under `--validate-goto-model`).

## Step 4: instrumenting CI

When the artifacts are not enough, a temporary commit can make CI collect
more, and a second one can restrict CI to the Visual Studio job to get
results within about an hour:

* `if: false` on every other job and workflow, and the VS 2026 job running
  only `ctest -L CORE -R "^cbmc-cpp-"`;
* a PowerShell script, run with `if: always()` after the tests and uploaded
  as an artifact, which for each failing test saves the cl-preprocessed
  source (`cbmc --preprocess`), a run with `--verbosity 9 --trace`,
  `--show-goto-functions`, `--show-symbol-table`, and the library dump of
  Step 3;
* diagnostics in the code itself, for instance printing both types in full
  when `goto_programt::validate` finds a symbol type inconsistency.

All such commits carry `TEMPORARY` in their subject and in a comment at
each change, and are reverted with `git revert` once the failures are
understood, so that `rg "TEMPORARY DEBUG" src` is empty again and the
workflows are unchanged.  On the branch of PR #8878, commits 1647625a10
(dump and script), 455da857a4 (CI restricted) and cca3cfd0be (types
printed) are examples; reverting their reverts (52ab318468, 5230bab136,
c9db057b79) restores them.

PowerShell scripts can be syntax-checked on Linux with the
`mcr.microsoft.com/powershell` Docker image before pushing.
