[![Build Status][travis_img]][travis] [![Build Status][appveyor_img]][appveyor]

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

License
=======
4-clause BSD license, see `LICENSE` file.

[travis]: https://travis-ci.org/diffblue/cbmc
[travis_img]: https://travis-ci.org/diffblue/cbmc.svg?branch=master
[appveyor]: https://ci.appveyor.com/project/diffblue/cbmc/
[appveyor_img]: https://ci.appveyor.com/api/projects/status/github/diffblue/cbmc?svg=true&branch=master