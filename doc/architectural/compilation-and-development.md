\ingroup module_hidden 
\page compilation-and-development Compilation and Development

\author Martin Brain, Peter Schrammel

\section compilation-and-development-section-compilation Compilation

The CBMC source code is available on
[its GitHub page](https://github.com/diffblue/cbmc).


\subsection compilation-and-development-subsection-makefiles Makefiles

Instructions for compiling CBMC using makefiles are
available in
[COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md#what-architecture)
in the root of the CBMC repository. They cover linux, Solaris 11,
FreeBSD 11, MacOS X and Windows.


\subsection compilation-and-development-subsection-cmake-files CMake files

There is experimental support for compiling using CMake. Instructions are
available in
[COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md#working-with-cmake-experimental)
in the root of the CBMC repository.


\subsection compilation-and-development-subsection-personal-configuration Personal configuration

\subsubsection compilation-and-development-subsubsection-config-inc config.inc

Two files,
[config.inc](https://github.com/diffblue/cbmc/blob/develop/src/config.inc) and
[common](https://github.com/diffblue/cbmc/blob/develop/src/common), are
included in every makefile. 
[config.inc](https://github.com/diffblue/cbmc/blob/develop/src/config.inc)
contains configuration options
relating to compilation so that they can be conveniently edited in one place.
[common](https://github.com/diffblue/cbmc/blob/develop/src/common)
contains commands that are needed in every makefile but which the
developer is not expected to edit. (There is also
[another config.inc](https://github.com/diffblue/cbmc/blob/develop/jbmc/src/config.inc)
which is also included in every makefile in the `jbmc` folder.) 
 

\subsubsection compilation-and-development-subsubsection-macro-debug Macro DEBUG

If the macro `DEBUG` is defined during compilation of CBMC (for example by
using a compiler flag) then extra debug code will be included. This includes
print statements and code checking that data structures are as expected.


\section compilation-and-development-section-running-tests Running tests

\subsection compilation-and-development-subsection-regression-tests Regression tests

The regression tests are contained in the `regression/` folder. Inside
`regression/` there is a directory for each of the tools/modules. Each of
these contains multiple test directories, with names describing
what they test. When there are multiple tests in a test directory then
they should all be testing the same thing. Each test directory contains
input files and one or more test description files,
which have the ending `.desc`. The test description files describe what command
to run, what output is expected and so on. The test framework is an in-house
Perl script,
[test.pl](https://github.com/diffblue/cbmc/blob/develop/regression/test.pl).
To run all the tests in a directory corresponding to a tool or module:

    ../test.pl -c PATH_TO_CBMC

The `--help` option to `test.pl` gives instructions for use and outlines the
format of the test description files.

If you have compiled CBMC using CMake then another way to run the same tests
is through `CTest`. From the build directory, the command `ctest -V -L CORE`
will run all of the tests that are run in CI. `-V` makes it print out more
useful output and `-L CORE` makes it only run tests that have been tagged
`CORE`. `-R regular_expression` can be used to limit which tests are run, and
`-N` makes it lists which tests it will run without actually running them. 


\subsection compilation-and-development-subsection-unit-tests Unit tests

The unit tests are contained in the `unit/` folder. They are written using the
[Catch](https://github.com/philsquared/Catch) unit test framework.

To run the unit tests for CBMC, go to `unit/` and run

    ../<build-folder>/bin/unit

To run the unit tests for JBMC, go to `jbmc/unit/` and run

    ../../<build-folder>/bin/java-unit

Note that some tests run which are expected to fail - see the summary at
the end of the run to see how many tests passed, how many failed which were
expected to and how many tests failed which were not expected to.

For more information on the structure of `unit/` and how to tag tests, see
[the section on unit tests in `Compiling.md` in the root of the CBMC
repository](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md#unit-tests)


\section compilation-and-development-section-documentation Documentation

Apart from the (user-orientated) CBMC user manual and this document, most
of the rest of the documentation is inline in the code as `doxygen` and
some comments. A man page for CBMC, goto-cc and goto-instrument is
contained in the `doc/` directory and gives some options for these
tools. All of these could be improved and patches are very welcome. In
some cases the algorithms used are described in the relevant papers.

The doxygen documentation can be [accessed online](http://cprover.diffblue.com).
To build it locally, run `doxygen` in `src/`. HTML output will be created in
`doc/html/`. The index page is `doc/html/index.html`.


\section compilation-and-development-section-formatting Formatting

The <a
href="https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md">
`CODING_STANDARD.md`</a> file in the root of the CBMC repository contains
guidance on how to write code for the CBMC repository. This includes
which language features can be used and formatting rules.

C++ code can be automatically reformatted in the correct way by running
`clang-format`. There are more details in
[CODING_STANDARD.md](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md#using-clang-format).


\section compilation-and-development-section-linting Linting

There is also a linting script, `scripts/cpplint.py`. There is a wrapper
script to run `cpplint.py` only on lines that have been changed from the
base branch:

    scripts/run_lint.sh <base-branch>

There are also instructions for adding this as a git pre-commit hook in
[CODING_STANDARD.md](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md#pre-commit-hook-to-run-cpplint-locally).
