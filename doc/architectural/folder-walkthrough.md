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
  * \ref goto-analyzer
  * \ref goto-instrument
  * \ref goto-diff
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

## Directory dependencies ##

This diagram shows *intended* directory dependencies.  Arrows should
be read transitively - dependencies of dependencies are often used
directly.

There are `module_dependencies.txt` files in each directory,
which are checked by the linter.  Where directories in `module_dependencies.txt`
are marked with comments such as 'dubious' or 'should go away', these
dependencies have generally not been included in the diagram.

\dot
digraph directory_dependencies {
  node [style = filled, color = white];

  subgraph cluster_executables {
    label = "Executables";
    style = filled;
    color = lightgrey;
    node [style = filled, color = white];
    CBMC [URL = "\ref cbmc"];
    goto_cc [label = "goto-cc", URL = "\ref goto-cc"];
    goto_analyzer [label = "goto-analyzer", URL = "\ref goto-analyzer"];
    goto_instrument [label = "goto-instrument", URL = "\ref goto-instrument"];
    goto_diff [label = "goto-diff", URL = "\ref goto-diff"];
    janalyzer [URL = "\ref janalyzer"];
    jdiff [URL = "\ref jdiff"];
    JBMC [URL = "\ref jbmc"];
    smt2_solver;
  }

  subgraph cluster_symbolic_execution {
    label = "Symbolic Execution";
    style = filled;
    color = lightgrey;
    node [style = filled, color = white];
    goto_symex [label = "goto-symex", URL = "\ref goto-symex"];
  }

  subgraph cluster_abstract_interpretation {
    label = "Abstract Interpretation";
    style = filled;
    color = lightgrey;
    node [style = filled, color = white];
    pointer_analysis [label = "pointer-analysis", URL = "\ref pointer-analysis"];
    analyses [URL = "\ref analyses"];
  }

  subgraph cluster_goto_programs {
    label = "Goto Programs";
    style = filled;
    color = lightgrey;
    goto_programs [label = "goto-programs", URL = "\ref goto-programs"];
    linking [URL = "\ref linking"];
  }

  subgraph cluster_solvers {
    label = "Solvers"
    style = filled;
    color = lightgrey;
    solvers [URL = "\ref solvers"];
  }

  subgraph cluster_languages {
    label = "Languages";
    style = filled;
    color = lightgrey;
    ansi_c [label = "ansi-c", URL = "\ref ansi-c"];
    langapi [URL = "\ref langapi"];
    cpp [URL = "\ref cpp"];
    jsil [URL = "\ref jsil"];
    java_bytecode [URL = "\ref java_bytecode"];  
  }

  subgraph cluster_utilities {
    label = "Utilities";
    style = filled;
    color = lightgrey;
    big_int [label = "big-int", URL = "\ref big-int"];
    miniz [URL = "\ref miniz"];
    util [URL = "\ref util"];
    nonstd [URL = "\ref nonstd"];
    json [URL = "\ref json"];
    xmllang [URL = "\ref xmllang"];
    assembler [URL = "\ref assembler"];
  }

  JBMC -> { CBMC, java_bytecode };
  jdiff -> { goto_diff, java_bytecode };
  janalyzer -> { goto_analyzer, java_bytecode };
  CBMC -> { goto_instrument, jsil };
  goto_diff -> { goto_instrument };
  goto_analyzer -> { analyses, jsil, cpp };
  goto_instrument -> { goto_symex, cpp };
  goto_cc -> { cpp, jsil };
  smt2_solver -> solvers;

  java_bytecode -> { analyses, miniz };
  jsil -> linking;
  cpp -> ansi_c;
  ansi_c -> langapi;
  langapi -> goto_programs;

  goto_symex -> { solvers, pointer_analysis };

  pointer_analysis -> { analyses, goto_programs };
  analyses -> pointer_analysis;

  solvers -> util;

  linking -> goto_programs;
  goto_programs -> { linking, xmllang, json, assembler };

  json -> util;
  xmllang -> util;
  assembler -> util;
  util -> big_int;
  util -> nonstd;
}
\enddot
