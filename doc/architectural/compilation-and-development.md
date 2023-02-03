\ingroup module_hidden 

\page compilation-and-development Compilation and Development

\author Martin Brain, Peter Schrammel, Owen Jones

\section compilation-and-development-section-compilation Compilation

The CBMC source code is available on
[its GitHub page](https://github.com/diffblue/cbmc).


\subsection compilation-and-development-subsection-makefiles Makefiles

Instructions for compiling CBMC using makefiles are
available in
[COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md#what-architecture)
in the root of the CBMC repository. They cover Linux, Solaris 11,
FreeBSD 11, MacOS X and Windows.


\subsection compilation-and-development-subsection-cmake-files CMake files

There is also support for compiling using CMake. Instructions are
available in
[COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md#working-with-cmake)
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

Note, these files are not involved in the CMake build.
 

\subsubsection compilation-and-development-subsubsection-macro-debug Macro DEBUG

If the macro `DEBUG` is defined during compilation of CBMC (for example by
using a compiler flag) then extra debug code will be included. This includes
print statements and code checking that data structures are as expected.


\section compilation-and-development-section-running-tests Running tests

\subsection compilation-and-development-subsection-regression-tests Regression tests

The regression tests are contained in `regression/` and `jbmc/regression/`.
Inside these folders there is a directory for each of the modules. Each
of these contains multiple test directories, with names describing
what they test. When there are multiple tests in a test directory then
they should all test very similar aspects of the program's behaviour. Each
test directory contains input files and one or more test description files,
which have the ending `.desc`. The test description files specify what command
to run, what output is expected and so on. The test framework is a
Perl script,
[test.pl](https://github.com/diffblue/cbmc/blob/develop/regression/test.pl),
located in `regression/test.pl`.

The `--help` option to `test.pl` outlines the
format of the test description files. Most importantly, the first word in a
test description file is its level, which is one of: `CORE` (should be run in
CI, should succeed), `THOROUGH` (takes too long to be run in CI, should
succeed), `FUTURE` (will succeed when a planned feature is added) or
`KNOWNBUG` (will succeed when a bug is fixed).

Test descriptions may also include a number of tags. `test.pl -I<tag>` will only
run tests with a particular `<tag>`, and `test.pl -X<tag>` will run all tests
except for those with a particular `<tag>`. See
[regression/README.md](https://github.com/diffblue/cbmc/blob/develop/regression/README.md)
for the current set of tags and their intended use.

\subsubsection compilation-and-development-subsubsection-running-regression-tests-with-make Running regression tests with make

If you have compiled using `make` then you can run the regression tests
using `make test`. Run it from `regression/` to run all the regression tests,
or any of its subfolders to just run the tests for that module. The number
of tests that are run in parallel can be controlled through the environment
variable `TESTPL_JOBS`.

If you have not compiled using `make` then this won't work, because the
makefile is expecting to find binaries like `cbmc` and `jbmc` in the source
folders.

\subsubsection compilation-and-development-subsubsection-running-regression-tests-with-ctest Running regression tests with CTest

If you have compiled using CMake then you can run the regression tests using
CTest. (Note: this will also run the unit tests.)

Here are two example commands, to be run from the `build/` directory:

    ctest -V -L CORE -R cpp
    ctest -V -L CORE -R cpp -E cbmc-cpp

`-V` makes it print out more
useful output. `-L CORE` makes it only run tests that have been tagged
`CORE`. `-R regular_expression` can be used to limit which tests are run to
those which match the given regular expression, and `-E regex` excludes tests
to those which match the given regular expression.
So the first command will run all the CORE tests in `regression/cbmc/cpp` and
`regression/cbmc/cbmc-cpp`, and the second will run all the CORE tests in
`regression/cbmc/cpp` only. Another useful option is `-N`, which makes CTest
list which tests it will run without actually running them.


\subsubsection compilation-and-development-subsubsection-running-individual-regression-tests-directly-with-test-pl Running individual regression tests directly with test.pl

It can be useful to run a single test folder in isolation. This can be done by
running `regression/test.pl` directly. The way that `test.pl` is run varies between the
different modules, and can be ascertained by looking at the `test` target in
the makefile. The simple case is when there isn't a file called `chain.sh`.
Then you can directly run `test.pl` on a single test folder with the
following command from the module directory (note that it is recommended to
use absolute paths as it avoids many issues, e.g. the path to the binary
should be relative to `<test-folder>`):

    <absolute-path-to-test.pl> -p -c <absolute-path-to-binary> <test-folder>

`-p` makes it print a log of failed tests and `-c` tells it where to find the
binary to run, e.g. `cbmc`, `jbmc` or `goto-analyzer`.
If `<test-folder>` is not provided then all test directories are run. The
`--help` option lists all command line options, including `-j` for running
multiple tests in parallel and `-C`, `-T`, `-F` and `-K` for controlling
whether `CORE`, `THOROUGH`, `FUTURE` or `KNOWNBUG` tests are run.

When there is a file called `chain.sh` then the command should look like

    <absolute-path-to-test.pl> -p -c '<absolute-path-to-chain-sh> <arg-1> ... <arg-n>' <test-folder>

Note that the test binary and its initial command line arguments are a single
value for the -c option, so they must be be wrapped in quotes if they contain
any unescaped spaces. What to put for the
arguments  `<arg-1>` to `<arg-n>` varies from module to module. To find
out, look in `chain.sh` and see what arguments it expects. You can also look in
the `Makefile` and see how it calls `chain.sh` in the `test` target.


\subsection compilation-and-development-subsection-unit-tests Unit tests

The unit tests are contained in the `unit/` folder. They are written using the
[Catch](https://github.com/philsquared/Catch) unit test framework.

If you have compiled with `make`, you can run the unit tests for CBMC directly
by going to `unit/`, running `make` to compile the unit tests and then
`make test` to run them. You can run the unit tests for JBMC directly by going
to `jbmc/unit/` and running the same commands.

If you have compiled with CMake, you can run the unit tests for CBMC directly
by going to `unit/` and running

    ../<build-folder>/bin/unit

and you can run the unit tests for JBMC directly by going to `jbmc/unit/` and
running

    ../../<build-folder>/bin/java-unit

If you have compiled with CMake you can also run the unit tests through CTest,
with the names `unit` and `java-unit`. So, from the `build/` directory, run

    ctest -V -L CORE -R ^unit
    ctest -V -L CORE -R java-unit

to run the CBMC unit tests and the JBMC unit tests respectively. (The `^` is
needed to make it a regular expression that matches `unit` but not `java-unit`.)

Note that some tests run which are expected to fail - see the summary at
the end of the run to see how many tests passed, how many failed which were
expected to and how many tests failed which were not expected to.

For more information on the structure of `unit/` and how to tag tests, see
[the section on unit tests in `CODING_STANDARD.md` in the root of the CBMC
repository](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md#unit-tests)


\subsection compilation-and-development-subsection-coverage Test coverage

On Unix-style systems you can automatically generate a code coverage report. To
obtain an HTML report for the test and unit tests, first build the dedicated
coverage configuration using CMake (setting `enable_coverage` and building the
`coverage` target):

    cmake -S . -Bcov-build -Denable_coverage=1 -Dparallel_tests=2
    make -C cov-build coverage

This configures a build environment in the `cov-build/` folder with coverage
recording at runtime enabled. The actual build (using `make` in the above case)
will run the test suite, running `parallel_tests`-many tests concurrently (in
the above case: 2). The HTML report is generated using `lcov` and stored in
`cov-build/html/`.


\subsection compilation-and-development-subsection-sat-solver Using a different SAT solver

By default, CBMC will assume MiniSat 2 as the SAT back-end. Several other
solvers are supported (see also
[config.inc](compilation-and-development-subsubsection-config-inc) above). As a
more general option, which is not limited to a single SAT solver, you may use
the IPASIR interface. For example, to use the SAT solver RISS, proceed as
follows:

1) Build RISS (in particular its IPASIR configuration):

    git clone https://github.com/conp-solutions/riss riss.git
    cd riss.git
    mkdir build
    cd build
    cmake ..
    make riss-coprocessor-lib-static
    cd ../..

2) Build CBMC while enabling the IPASIR back-end:
    make -C src IPASIR=../../riss.git/riss \
      LIBS="../../riss.git/build/lib/libriss-coprocessor.a -lpthread"

3) Run CBMC - note that RISS is highly configurable via the RISSCONFIG
environment variable:
    export RISSCONFIG=VERBOSE:BMC1
    ... run CBMC ...


\section compilation-and-development-section-documentation Documentation

Apart from the (user-orientated) CBMC user manual and this document, most
of the rest of the documentation is inline in the code as `doxygen` and
some comments. A man page for CBMC, goto-cc and goto-instrument is
contained in the `doc/` directory and gives some options for these
tools. All of these could be improved and patches are very welcome. In
some cases the algorithms used are described in the relevant papers.

The doxygen documentation can be [accessed online](https://diffblue.github.io/cbmc/).
To build it locally, run `scripts/run_doxygen.sh`.  HTML output will be created
in `doc/html/`. The index page is `doc/html/index.html`.  This script will
filter out expected warning messages from doxygen, so that new problems are more
obvious.  It is important to use the correct version of doxygen, as specified
in `run_doxygen.sh`, so that there are no unexpected changes to the list of
expected warnings.  In the event that any change fixes an old warning, then the 
corresponding line(s) should be deleted from
`scripts/expected_doxygen_warnings.txt`.  We want to avoid adding any more
warnings to this list of expected warnings, but that can be done to work around
limitations in Doxygen (where the code and documentation are completely correct).


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
script to run `cpplint.py` only on lines that differ from another
branch, e.g. to run it on lines that have been changed from `develop`:

    scripts/run_lint.sh develop

There are also instructions for adding this as a git pre-commit hook in
[CODING_STANDARD.md](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md#pre-commit-hook-to-run-cpplint-locally).


\section compilation-and-development-section-time-profiling Time profiling

To do time profiling with a tool like `gprof`, the flags `-g` (build with debug
symbols) and `-pg` (enable profiling information) must be
used when compiling, and `-pg` must be used when linking. If you are building
with cmake you can just add "-Denable_profiling=1" to your cmake invocation, and
reload cmake before building your desired binary. Note that these flags require
everything to be rebuilt, so it will take a long time even if you are using
ccache.

Run your binary as normal. A file called gmon.out will be created in the
working directory of the binary at the end of execution. In most instances this
will be the same as the working directory at the beginning of execution. It is
also possible to choose the output location by setting the environment variable
GMON_OUT_PREFIX - the output file location is then whatever you set it to with
the process id appended to the end.

Make sure gprof is installed by running `gprof -v`. If it is not installed then
run `sudo apt install binutils`.

Run `gprof <path-to-binary> <path-to-gmon.out>` and redirect the output to a
file. This will take a while to run - e.g. 12 minutes for test-gen run on a
trivial function.

The output file will now be a large text file. There are two sections: the "flat
profile", which ignores context, and just tells you how much time was spent in
each function; and the "call graph", which includes context, and tells you how
much time was spent within each call stack. For more information see online
tutorials, like
https://ftp.gnu.org/old-gnu/Manuals/gprof-2.9.1/html_chapter/gprof_5.html
