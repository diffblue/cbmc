\ingroup module_hidden 
\page folder-walkthrough Folder Walkthrough

\author Martin Brain, Peter Schrammel

## `src/` ##

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

## `doc/` ##

Contains the CBMC man page. Doxygen HTML pages are generated
into the `doc/html` directory when running `doxygen` from `src`.

## `regression/` ##

The `regression/` directory contains the regression test suites. See
\ref compilation-and-development for information on how to run and
develop regression tests.

## `unit/` ##

The `unit/` directory contains the unit test suites. See
\ref compilation-and-development for information on how to run and
develop unit tests.
