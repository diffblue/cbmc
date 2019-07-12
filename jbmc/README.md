About
=====

JBMC is a Bounded Model Checker for Java programs. It supports
checking for runtime exceptions and user-defined assertions.
The verification is performed by unwinding the loops in the program
and passing the resulting equation to a decision procedure.

[More info...](http://www.cprover.org/jbmc)

Versions
========

Get the [latest release](https://github.com/diffblue/cbmc/releases)
* Releases are tested and for production use.

Get the current *develop* version: `git clone https://github.com/diffblue/cbmc.git`
* Develop versions are not recommended for production use.

Prerequisites
============

JBMC compiles CBMC as part of its build process and as such has all the pre-requisites of CBMC. These can be viewed at: [diffblue/cbmc:COMPILING](http://github.com/diffblue/cbmc/blob/master/COMPILING)

Compilation
===========

Before compilation, run the commands:

```bash
make -C src DOWNLOADER=wget minisat2-download
make -C jbmc/src setup-submodules
```

Then compile using:

```bash
make -C jbmc/src
```

Output
======

Compiling produces an executable called `jbmc` which by default can be found in `jbmc/src/jbmc/jbmc`

Reporting bugs and contributing to the code base
================================================

See [CBMC](https://github.com/diffblue/cbmc/blob/develop/README.md))

License
=======
4-clause BSD license, see `LICENSE` file.
