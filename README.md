[![Build Status][build_img]][travis]

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

[build_img]: https://travis-ci.org/tautschnig/cbmc.svg?branch=master
[travis]: https://travis-ci.org/tautschnig/cbmc
