## Overview of CProver Tools

This document provides a brief overview of the various tools in
the CProver project. The goal is as to provide a lightweight reference
with links to detailed documentation on each of the tools.

The tools in the CProver project are as follows:
- [cbmc](#cbmc)
- [goto-analyzer](#goto-analyzer)
- [goto-cc (goto-gcc, goto-ld)](#goto-cc)
- [goto-diff](#goto-diff)
- [goto-harness](#goto-harness)
- [goto-instrument](#goto-instrument)
- [janalyzer](#janalyzer)
- [jbmc](#jbmc)
- [jdiff](#jdiff)
- [memory-analyzer](#memory-analyzer)
- [smt2_solver](#smt2_solver)
- [symtab2gb](#symtab2gb)
- [Developer Utilities](#developer-utilities)
    - [java-unit](#java-unit)
    - [unit](#unit)
    - [others (converter, driver, file_converter, java-converter)](#others)

The rest of this document provides a section on each of these tools in alphabetical order.
Most links in this document are to the [CProver online documentation](http://cprover.diffblue.com/index.html).


## cbmc

The C Bounded Model Checker (`cbmc`) is the main tool used in the CProver suite.
`cbmc` does the entire analysis from the source code through to the result,
including generating traces. This includes invoking various sub-tools and 
modules.

For details on usage of the `cbmc` tool see the following documentation
- [Developer Tutorial](http://cprover.diffblue.com/tutorial.html)
includes a very brief tutorial on many aspects of `cbmc` and other tools.

For details on the architecture of the `cbmc` tool and how the analysis is performed
see the following documents:
- [CBMC Architecture](http://cprover.diffblue.com/cbmc-architecture.html)
gives a high level overview of the `cbmc` architecture and data flow.
- [Background Concepts](http://cprover.diffblue.com/background-concepts.html)
overviews all the key concepts used in the `cbmc` analysis.

For details on compiling, testing, contributing, and documentation related to 
development see:
- [CProver Developer Documentation](http://cprover.diffblue.com/index.html)


## goto-analyzer

The `goto-analyzer` is a wrapper program around the
[abstract interpretation](http://cprover.diffblue.com/background-concepts.html#abstract_interpretation_section)
implementations. (For more detail on these implementations see
[here](http://cprover.diffblue.com/group__analyses.html).)
It is possible to configure which abstractions are used and what
is done with the chosen abstractions (verification, display,
simplification, etc.). The current best documentation is available
[here](http://cprover.diffblue.com/goto__analyzer__parse__options_8h.html).

Other documentation useful for this tool can be found:
- [Analysis Information](http://cprover.diffblue.com/group__analyses.html)

Details of all the options can be seen by running
```
goto-analyzer --help
```

## goto-cc

This is a compiler designed to be able to be dropped in to an existing
build process to replace the existing compiler. `goto-cc` is able to do
normal compilation, but is designed to output goto programs (optionally
in addition to the normal compiled program). Note that `goto-cc` is both
the compiler and linker (`goto-gcc` and `goto-ld` are symbolic links to
`goto-cc`, where the file name is used to ensure the program behaves
according to the name, e.g. if called from `goto-gcc` then `goto-cc`
will behave like `gcc`). The additional object code is used as the internal
representation for `cbmc` and related tools. These can also be extracted and
used themselves.

Further information on `goto-cc` can be found:
- [Developer Tutorial](http://cprover.diffblue.com/tutorial.html) with
some very simple examples and notes.
- [goto-cc](http://cprover.diffblue.com/group__goto-cc.html) information
on the `goto-cc` compilers
- [goto Programs](http://cprover.diffblue.com/group__goto-programs.html)
for information on goto programs and how they are used.

Note that `goto-cc` can emulate GCC, Visual Studio, and CodeWarrior
compilers.


## goto-diff

Provides a variety of difference checks between two goto programs
produced by `goto-cc` (essentially a `diff` tool for goto programs).
This invokes some of the cbmc tools to convert the goto
program and then determine which functions are added/removed/changed.

Details of all the options can be seen by running
```
goto-diff --help
```
this includes both options for the difference, and options for the goto
program instrumentation.


## goto-harness

This is a tool for creating a harness around a (part of a) goto program that
can then be analysed (using the harness). Harnesses can be either function
call environments, or memory snapshots. 

Documentation on `goto-harness` can be found
[here](http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_goto-harness.html)
including details and examples.

Details of all the options can be seen by running
```
goto-harness --help
```


## goto-instrument

This is a collection of tools for analysing and modifying goto programs 
(programs created with #goto-cc). Generally these take a goto program 
and output another goto program.

Further examples and documentation can be found:
- [goto-instrument](http://cprover.diffblue.com/group__goto-instrument.html)
has an overview of `goto-instrument` and a small tutorial example.
- [Developer Tutorial](http://cprover.diffblue.com/tutorial.html) has high
level overview and some example commands for `goto-instrument`.


## janalyzer

This provides a way to access and invoke various forms of analysis on
Java programs. This is a fork of [goto-analyzer](#goto-analyzer) with
a Java Virtual Machine front end.

Documentation useful for this tool can be found:
- [Analysis Information](http://cprover.diffblue.com/group__analyses.html)

Details of all the options can be seen by running
```
janalyzer --help
```


## jbmc

This is the main analysis engine the performs the analysis
of Java files using bounded model checking. This is a
version of the `cbmc` tool that checks Java programs
(more documentation for `cbmc` is available and much of
it applies to `jbmc` since they use many of the same back
end utilities).

Note that the `jbmc` tool follows `java` conventions so that
programs can be analyzed in the same way you would run them
using the `java` executable. There also many additional
options to support nondeterministic initialisation of variable
size arrays, data structures and strings, control how to assert
on exceptions etc.

For some light information on usage of the jbmc tool see the following documentation
- [JBMC homepage](https://www.cprover.org/jbmc/) includes some
simple examples and information.

For details on how analysis is performed in the `cbmc` and
`jbmc` tools see see the following documents:
- [CBMC Architecture](http://cprover.diffblue.com/cbmc-architecture.html)
gives a high level overview of the `cbmc` architecture and data flow that *should also apply to* `jbmc`.
- [Background Concepts](http://cprover.diffblue.com/background-concepts.html)
overviews all the key concepts used in the `jbmc` analysis.

For details on compiling, testing, contributing, and documentation related to development see:
- [CProver Development Documentation](http://cprover.diffblue.com/index.html)


## jdiff

Provides a variety of difference checks between two goto programs (produced
by `goto-cc`). This invokes some of the `cbmc`/`jbmc` tools to convert the goto
program and then determine which functions are added/removed/changed.
This is a clone of `goto-diff` for Java programs and is essentially
a `diff` for goto programs generated from Java code.

Details of all the options can be seen by running
```
jdiff --help
```
this includes both options for the difference, and options for the goto
program instrumentation.


## memory-analyzer

This is a wrapper program that provides a front end to `gdb` that adds some
useful features related to the other goto utilities. In particular
`memory-analyzer` can run a compiled binary using `gdb` and then (at the
right point) create a harness from the current program state for use with
`goto-harness`.

Note that to use `memory-analyzer` the program must be compiled with
`goto-cc`. To make best use of `memory-analyzer` and `gdb` you should
compile with the `-g` option. 

For further documentation and examples see 
[here](http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_memory-analyzer.html).


## smt2_solver

This is an (Satisfiability Modulo Theories) SMT solver that
parses SMT-LIB 2 format files and uses CProver's internal bit-blasting
solver (see [solvers](http://cprover.diffblue.com/group__solvers.html))
to resolve queries.

## symtab2gb

This utility is to compile a cbmc symbols table (in JSON format) into a goto binary.
This is to support integration of external language frontends
(e.g. [Ada using GNAT2GOTO](https://github.com/diffblue/gnat2goto/)).
For usage run
```
symtab2gb --help
```


## Developer Utilities

The utilities below are designed for developer use.

### java-unit

Runs Java unit tests. For more details use
```
java-unit --help
```
Default behaviour is to only show failed test cases.


### unit

Runs C unit tests. For more details use
```
unit --help
```
Default behaviour is to only show failed test cases.

