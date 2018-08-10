\ingroup module_hidden 
\page compilation-and-development Compilation and Development

\author Martin Brain, Peter Schrammel

## Makefiles ##

First off, read the \ref cbmc-user-manual "CBMC User Manual". It describes
how to get, build and use CBMC. This document covers the
internals of the system and how to get started on development.

## CMake files ##

To be documented.

## Personal configuration: config.inc, macro DEBUG ##

To be documented.

## Running tests ##

### Regression tests ###

The regression tests are contained in the `regression/` folder.
They are grouped into directories for each of the tools/modules.
Each of these contains a directory per test case, containing a C or C++
file that triggers the bug and a `.desc` file that describes
the tests, expected output and so on. There is a Perl script,
`test.pl` that is used to invoke the tests as:

    ../test.pl -c PATH_TO_CBMC

The `–help` option gives instructions for use and the
format of the description files.

To be documented further.

### Unit tests ###

To be documented.

## Documentation ##

Apart from the (user-orientated) CBMC user manual and this document, most
of the rest of the documentation is inline in the code as `doxygen` and
some comments. A man page for CBMC, goto-cc and goto-instrument is
contained in the `doc/` directory and gives some options for these
tools. All of these could be improved and patches are very welcome. In
some cases the algorithms used are described in the relevant papers.

## Accessing doxygen documentation ##

The doxygen documentation can be [accessed online](http://cprover.diffblue.com).
To build it locally, run `doxygen` in `/src`. HTML output will be created in
`/doc/html`. The index page is `/doc/html/index.html`.

## Coding standards ##

See <a
href="https://github.com/diffblue/cbmc/blob/master/CODING_STANDARD.md">
`CODING_STANDARD.md`</a> file in the root of the CBMC repository.

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