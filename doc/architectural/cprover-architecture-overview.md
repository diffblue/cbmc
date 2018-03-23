\ingroup module_hidden 
\page cprover-architecture-overview CProver Architecture Overview

\author Martin Brain, Peter Schrammel

\section overview-dirs Overview of CPROVER Directories

## `src/`

The source code is divided into a number of sub-directories, each
containing the code for a different part of the system.

- GOTO-Programs

  * \ref goto-programs
  * \ref linking

- Symbolic Execution
  * \ref goto-symex

- Static Analyses

  * \ref analyses
  * \ref pointer-analysis

- Solvers
  * \ref solvers

- Language Front Ends

  * Language API: \ref langapi
  * C: \ref ansi-c
  * C++: \ref cpp
  * Java: \ref java_bytecode
  * JavaScript: \ref jsil

- Tools

  * \ref cbmc
  * \ref clobber
  * \ref goto-analyzer
  * \ref goto-instrument
  * \ref goto-diff
  * \ref memory-models
  * \ref goto-cc
  * \ref jbmc

- Utilities

  * \ref big-int
  * \ref json
  * \ref xmllang
  * \ref util
  * \ref miniz
  * \ref nonstd

In the top level of `src` there are only a few files:

* `config.inc`:   The user-editable configuration parameters for the
  build process. The main use of this file is setting the paths for the
  various external SAT solvers that are used. As such, anyone building
  from source will likely need to edit this.

* `Makefile`:   The main systems Make file. Parallel builds are
  supported and encouraged; please don’t break them!

* `common`:   System specific magic required to get the system to build.
  This should only need to be edited if porting CBMC to a new platform /
  build environment.

* `doxygen.cfg`:   The config file for doxygen.cfg

## `doc/`

Contains the CBMC man page. Doxygen HTML pages are generated
into the `doc/html` directory when running `doxygen` from `src`.

## `regression/`

The `regression/` directory contains the test suites.
They are grouped into directories for each of the tools/modules.
Each of these contains a directory per test case, containing a C or C++
file that triggers the bug and a `.desc` file that describes
the tests, expected output and so on. There is a Perl script,
`test.pl` that is used to invoke the tests as:

    ../test.pl -c PATH_TO_CBMC

The `–help` option gives instructions for use and the
format of the description files.


\section general-info General Information

First off, read the \ref cbmc-user-manual "CBMC User Manual". It describes
how to get, build and use CBMC. This document covers the
internals of the system and how to get started on development.

## Documentation

Apart from the (user-orientated) CBMC user manual and this document, most
of the rest of the documentation is inline in the code as `doxygen` and
some comments. A man page for CBMC, goto-cc and goto-instrument is
contained in the `doc/` directory and gives some options for these
tools. All of these could be improved and patches are very welcome. In
some cases the algorithms used are described in the relevant papers.

## Architecture

This section provides a graphical overview of how CBMC fits together.
CBMC takes C code or a goto-binary as input and tries to emit traces
of executions that lead to crashes or undefined behaviour. The diagram
below shows the intermediate steps in this process.

\dot
digraph G {

  rankdir="TB";
  node [shape=box, fontcolor=blue];

  subgraph top {
    rank=same;
    1 -> 2 -> 3 -> 4;
  }

  subgraph bottom {
    rank=same;
    5 -> 6 -> 7 -> 8 -> 9;
  }

  /* shift bottom subgraph over */
  9 -> 1 [color=white];

  4 -> 5;

  1 [label="command line\nparsing" URL="\ref cbmc_parse_optionst"];
  2 [label="preprocessing,\nparsing" URL="\ref preprocessing"];
  3 [label="language\ntype-checking" URL="\ref type-checking"];
  4 [label="goto\nconversion" URL="\ref goto-conversion"];
  5 [label="instrumentation" URL="\ref instrumentation"];
  6 [label="symbolic\nexecution" URL="\ref symbolic-execution"];
  7 [label="SAT/SMT\nencoding" URL="\ref sat-smt-encoding"];
  8 [label="decision\nprocedure" URL="\ref decision-procedure"];
  9 [label="counter example\nproduction" URL="\ref counter-example-production"];
}
\enddot

The \ref cbmc-user-manual "CBMC User Manual" describes CBMC from a user
perspective. Each node in the diagram above links to the appropriate
class or module documentation, describing that particular stage in the
CBMC pipeline.
CPROVER is structured in a similar fashion to a compiler. It has
language specific front-ends which perform limited syntactic analysis
and then convert to an intermediate format. The intermediate format can
be output to files (this is what `goto-cc` does) and are (informally)
referred to as “goto binaries” or “goto programs”. The back-end are
tools process this format, either directly from the front-end or from
it’s saved output. These include a wide range of analysis and
transformation tools (see \ref other-tools).

## Coding Standards

See `CODING_STANDARD.md` file in the root of the CBMC repository.

CPROVER is written in a fairly minimalist subset of C++; templates and
meta-programming are avoided except where necessary.
External library dependencies are avoided (only STL and a SAT solver
are required). Boost is not used. The `util` directory contains many
utilities that are not (yet) in the standard library.

Patches should be formatted so that code is indented with two space
characters, not tab and wrapped to 80 columns. Headers for doxygen
should be given (and preferably filled!) and the author will be the
person who first created the file. Add doxygen comments to
undocumented functions as you touch them. Coding standards
and doxygen comments are enforced by CI before a patch can be
merged by running `clang-format` and `cpplint`.

Identifiers should be lower case with underscores to separate words.
Types (classes, structures and typedefs) names must end with a `t`.
Types that model types (i.e. C types in the program that is being
interpreted) are named with `_typet`. For example `ui_message_handlert`
rather than `UI_message_handlert` or `UIMessageHandler` and
`union_typet`.


\section other-tools Other Tools

FIXME: The text in this section is a bit outdated.

The CPROVER subversion archive contains a number of separate programs.
Others are developed separately as patches or separate
branches.Interfaces are have been and are continuing to stablise but
older code may require work to compile and function correctly.

In the main archive:

* `CBMC`:   A bounded model checking tool for C and C++. See 
  \ref cbmc.

* `goto-cc`:   A drop-in, flag compatible replacement for GCC and other
  compilers that produces goto-programs rather than executable binaries.
  See \ref goto-cc.

* `goto-instrument`:   A collection of functions for instrumenting and
  modifying goto-programs. See \ref goto-instrument.

Model checkers and similar tools:

* `SatABS`:   A CEGAR model checker using predicate abstraction. Is
  roughly 10,000 lines of code (on top of the CPROVER code base) and is
  developed in its own subversion archive. It uses an external model
  checker to find potentially feasible paths. Key limitations are
  related to code with pointers and there is scope for significant
  improvement.

* `Scratch`:   Alistair Donaldson’s k-induction based tool. The
  front-end is in the old project CVS and some of the functionality is
  in `goto-instrument`.

* `Wolverine`:   An implementation of Ken McMillan’s IMPACT algorithm
  for sequential programs. In the old project CVS.

* `C-Impact`:   An implementation of Ken McMillan’s IMPACT algorithm for
  parallel programs. In the old project CVS.

* `LoopFrog`:   A loop summarisation tool.

* `TAN`:   Christoph’s termination analyser.

Test case generation:

* `cover`:   A basic test-input generation tool. In the old
    project CVS.

* `FShell`:   A test-input generation tool that allows the user to
  specify the desired coverage using a custom language (which includes
  regular expressions over paths). It uses incremental SAT and is thus
  faster than the naïve “add assertions one at a time and use the
  counter-examples” approach. Is developed in its own subversion.

Alternative front-ends and input translators:

* `Scoot`:   A System-C to C translator. Probably in the old
    project CVS.

* `???`:   A Simulink to C translator. In the old project CVS.

* `???`:   A Verilog front-end. In the old project CVS.

* `???`:   A converter from Codewarrior project files to Makefiles. In
    the old project CVS.

Other tools:

* `ai`:   Leo’s hybrid abstract interpretation / CEGAR tool.

* `DeltaCheck?`:   Ajitha’s slicing tool, aimed at locating changes and
  differential verification. In the old project CVS.

There are tools based on the CPROVER framework from other research
groups which are not listed here.
