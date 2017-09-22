[![Build Status][travis_img]][travis] [![Build Status][appveyor_img]][appveyor]
[![Build Status][coverity_img]][coverity]

[CProver Wiki](http://www.cprover.org/wiki)

About
=====

CBMC is a Bounded Model Checker for C and C++ programs. It supports C89, C99,
most of C11 and most compiler extensions provided by gcc and Visual Studio. It
also supports SystemC using Scoot. It allows verifying array bounds (buffer
overflows), pointer safety, exceptions and user-specified assertions.
Furthermore, it can check C and C++ for consistency with other languages, such
as Verilog. The verification is performed by unwinding the loops in the program
and passing the resulting equation to a decision procedure.

For full information see [cprover.org](http://www.cprover.org/cbmc).

Versions
========

Get the [latest release](https://github.com/diffblue/cbmc/releases)
* Releases are tested and for production use.

Get the current *develop* version: `git clone https://github.com/diffblue/cbmc.git`
* Develop versions are not recommended for production use.

Report bugs
===========

If you encounter a problem please file a bug report:
* Create an [issue](https://github.com/diffblue/cbmc/issues)

Contributing to the code base
=============================

1. Fork the repository
2. Clone the repository `git clone git@github.com:YOURNAME/cbmc.git`
3. Create a branch from the `develop` branch (default branch)
4. Make your changes (follow the [coding guidelines](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md))
5. Push your changes to your branch
6. Create a Pull Request targeting the `develop` branch

License
=======
4-clause BSD license, see `LICENSE` file.

[travis]: https://travis-ci.org/diffblue/cbmc
[travis_img]: https://travis-ci.org/diffblue/cbmc.svg?branch=master
[appveyor]: https://ci.appveyor.com/project/diffblue/cbmc/
[appveyor_img]: https://ci.appveyor.com/api/projects/status/github/diffblue/cbmc?svg=true&branch=master
[coverity]: https://scan.coverity.com/projects/diffblue-cbmc
[coverity_img]: https://scan.coverity.com/projects/13552/badge.svg
