[![Build Status][travis_img]][travis]
![Build Status][codebuild_img]
![Build Status][codebuild_windows_img]

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

[travis]: https://travis-ci.org/diffblue/cbmc
[travis_img]: https://travis-ci.org/diffblue/cbmc.svg?branch=develop
[codebuild_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoieVl4UDBKaVU2NEZIeE9GKzhMVWJUQ1RORXRZeGFEdm9LZnhvbWt4Q3oxb29uOTdWZDhZUkUvK2Z0eTBndU5pWkcyUXFZb1pDRVpBNXVob3R0R2tYZkdFPSIsIml2UGFyYW1ldGVyU3BlYyI6IkZ0TzR2a21XbHFkWnlYMkwiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
[codebuild_windows_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiTFQ4Q0lCSEc1Rk5NcmlzaFZDdU44Vk8zY0c1VCtIVWMwWnJMRitmVFI5bE94Q3dhekVPMWRobFU2Q0xTTlpDSWZUQ3J1eksrWW1rSll1OExXdll2bExZPSIsIml2UGFyYW1ldGVyU3BlYyI6InpqcloyaEdxbjBiQUtvNysiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
