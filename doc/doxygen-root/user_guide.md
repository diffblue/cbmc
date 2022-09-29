\page user_guide User Guide

For a quick start with CBMC on simple problems, read

* The \ref installation_guide
* A [short tutorial](cprover-manual/md_cbmc-tutorial.html)
* A [short manual](cprover-manual/index.html)

For a quick start with CBMC on large software projects, read

* [Deploying CBMC on industrial software projects](https://model-checking.github.io/cbmc-training)
  describing how to use CBMC as part of routine software development and
  continuous integration.

Two third-party tools simplify using CBMC:

* [CBMC Viewer](https://model-checking.github.io/cbmc-viewer)
  scans the output of CBMC and produces a browsable summary of its findings.
* [CBMC Starter Kit](https://model-checking.github.io/cbmc-starter-kit)
  makes it easy to add CBMC verification to an existing software project.

Key concepts:

* The \ref reference_guide describes CBMC and the CBMC tool chain
* CBMC [primitives](cprover-manual/md_api.html) and
  [memory primitives](cprover-manual/md_memory-primitives.html)
  are useful when writing CBMC assumptions and CBMC assertions.
* \ref goto-programs "goto programs" are the intermediate representation
  of C code used by the CBMC tool chain
* \ref goto-cc "goto-cc" ([man page](man/goto-cc.html))
  compiles C into the goto program used by CBMC.
  It is intended to be a drop-in replacement for `gcc` and `cl`.
* \ref goto-instrument "goto-instrument" ([man page](man/goto-instrument.html))
  is a collection of tools for
  modifying goto programs.  One example is unwinding loops in a goto program.
* \ref goto-analyzer "goto-analyser" ([man page](man/goto-analyzer.html))
  is a collection of tools for analyzing goto programs.
  One example is finding the set of reachable functions in a goto program.

Please \ref contributing_documentation "contribute documentation"
when you find mistakes or missing information to help us improve this
user guide.
