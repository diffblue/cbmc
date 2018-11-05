Here a few minimalistic coding rules for the CPROVER source tree.

# Whitespaces

Formatting is enforced using clang-format. For more information about this, see
`COMPILING.md`. A brief summary of the formatting rules is given below:

- Use 2 spaces indent, no tabs.
- No lines wider than 80 chars.
  - When line is wider, do the following:
    - Subsequent lines should be indented two more than the initial line
    - Break after `=` if it is part of an assignment
      - For chained calls, prefer immediately before `.`
    - For other operators (e.g. `&&`, `+`) prefer immediately after the
      operator
    - For brackets, break after the bracket
      - In the case of function calls, put each argument on a separate line if
        they do not fit after one line break
      - Nested function calls do not need to be broken up into separate lines
        even if the outer function call does.
- If a method is bigger than 50 lines, break it into parts.
- Put matching `{ }` into the same column, except for initializer lists and
  lambdas, where you should place `{` directly after the closing `)`. This is
  to comply with clang-format, which doesn't support aligned curly braces in
  these cases.
- Spaces around binary operators (`=`, `+`, `==` ...)
- Space after comma (parameter lists, argument lists, ...)
- Space after colon inside `for`
- For pointers and references, the `*`/`&` should be attached to the variable
  name as opposed to the type. E.g. for a pointer to an int the syntax would
  be: `int *x;`
- No whitespaces at end of line
- No whitespaces in blank lines
- Put argument lists on next line (and indent 2 spaces) if too long
- Put parameters on separate lines (and indent 2 spaces) if too long
- Spaces around colon for inheritance, put inherited into separate lines in
  case of multiple inheritance
- The initializer list follows the constructor with a whitespace around the
  colon.
- `if(...)`, `else`, `for(...)`, `do`, and `while(...)` are always in a
  separate line
- Break expressions in `if`, `for`, `while` if necessary and align them with
  the first character following the opening parenthesis
- Use `{}` instead of `;` for the empty statement
- Single line blocks without `{ }` are allowed, but put braces around
  multi-line blocks
- Use blank lines to visually separate logically cohesive code blocks within a
  function
- Have a newline at the end of a file

# Comments
- Do not use `/* */`
- Each source and header file must start with a comment block stating the
  author. See existing source for an example of the format of this block. This
  should be followed by a Doxygen `\file` comment:
  ```c++
  /// \file
  /// <Some information about this file goes here>
  ```
  Note that the `\file` tag must be immediately followed by a newline in order
  for Doxygen to relate the comment to the current file.
- Each class, member variable and function should be preceded by a Doxygen
  comment describing it when it is not immediately obvious what it does. The
  format should match the [LLVM
  guidelines](http://llvm.org/docs/CodingStandards.html#doxygen-use-in-documentation-comments),
  with one extension: for functions, `\param` and `\return` comments longer than
  a single line should have subsequent lines indented by two spaces, so that the
  tags stand out. An example:
  ```c++
  /// This sentence, until the first dot followed by whitespace, becomes
  /// the brief description. More detailed text follows. Feel free to
  /// break this into paragraphs to aid readability.
  /// \param arg_name: This parameter doesn't need much description
  /// \param [out] long_arg_name: This parameter is mutated by the function.
  ///   Extra info about the parameter gets indented an extra two columns,
  ///   like this.
  /// \return The return value is literally the value returned by the
  ///   function. For out-parameters, use "\param [out]".
  return_typet my_function(argt arg_name, argt &long_arg_name)
  ```
- The priority of documentation is readability. Therefore, feel free to use
  Doxygen features, or to add whitespace for multi-paragraph comment blocks if
  necessary.
- For functions or methods that provide an interface to a module, a comment
  block should immediately precede the declaration of the entity
  it documents. This implies that it will live in the header file.
  The documentions should focus on the externally visible behavior, and
  should discuss the implementation only to the extent necessary for
  understanding usage. The implementation should be explained using
  comments in the definition of the function or method.
- Functions or methods that are internal to a module are documented in a
  comment block that precedes the definition.
- The documentation block must *immediately* precede the entity it documents.
  Don't insert empty lines between docs and functions, because this will
  confuse Doxygen.
- Put comments on a separate line
- Use comments to explain the non-obvious
- Use #if 0 for commenting out source code
- Use #ifdef DEBUG to guard debug code

# Naming
- Identifiers should make clear the purpose of the thing they are naming. 
- Identifiers may use the characters `[a-z0-9_]` and should start with a
  lower-case letter (parameters in constructors may start with `_`).
- Omit names of parameters or exception objects when they are not used. If
  parameter names help documenting an interface, keep the name and use
  `(void)parameter_name;` in the body of the method.
- Use American spelling for identifiers.
- Separate basic words by `_`
- Avoid abbreviations (e.g. prefer `symbol_table` to `st`).
- User defined type identifiers have to be terminated by `t`. Moreover, before
  `t` may not be `_`.
- Do not use `m_` prefix nor `_` suffix for names of attributes of structured
  types.
- Enum values may use the characters `[A-Z0-9_]`

# Header files
- Avoid unnecessary `#include`s, especially in header files
- Prefer forward declaration to includes, but forward declare at the top of the
  header file rather than in line
- Guard headers with `#ifndef CPROVER_DIRECTORIES_FILE_H`, etc
- The corresponding header for a given source file should always be the *first*
  include in the source file. For example, given `foo.h` and `foo.cpp`, the
  line `#include "foo.h"` should precede all other include statements in
  `foo.cpp`.
- Use the C++ versions of C headers (e.g. `cmath` instead of `math.h`).
  Some of the C headers use macros instead of functions which can have
  unexpected consequences.

# Makefiles
- Each source file should appear on a separate line
- The final source file should still be followed by a trailing slash
- The last line should be a comment to not be deleted, i.e. should look like:
  ```makefile
  SRC = source_file.cpp \
        source_file2.cpp \
        # Empty last line
  ```
  This ensures the Makefiles can be easily merged.

# Program Command Line Options
- Each program contains a `program_name_parse_optionst` class which should
  contain a define `PROGRAM_NAME_PARSE_OPTIONS` which is a string of all the
  parse options in brackets (with a colon after the bracket if it takes a
  parameter)
- Each parameter should be one per line to yield easy merging
- If parameters are shared between programs, they should be pulled out into a
  common file and then included using a define
- The defines should be `OPT_FLAG_NAMES` which should go into the `OPTIONS`
  define
- The defines should include `HELP_FLAG_NAMES` which should contain the help
  output in the format:
  ```
  " --flag                explanations\n" \
  " --another flag        more explanation\n" \
   <-------30 chars------>
  ```
- The defines may include `PARSE_OPTIONS_FLAG_NAMES` which move the options
  from the command line into the options

# C++ features
- Do not use namespaces, except for anonymous namespaces.
- Prefer use of `using` instead of `typedef`.
- Prefer use of `class` instead of `struct`.
- Write type modifiers before the type specifier.
- Make references `const` whenever possible
- Make member functions `const` whenever possible
- Do not hide base class functions
- When overriding a virtual function, use `override` (without `virtual`)
- Single argument constructors must be `explicit`
- Avoid implicit conversions
- Avoid `friend` declarations
- Avoid iterators, use ranged `for` instead
- Avoid allocation with `new`/`delete`, use `unique_ptr`
- Avoid pointers, use references
- Avoid `char *`, use `std::string`
- For numbers, use `int`, `unsigned`, `long`, `unsigned long`, `double`
- Use `mp_integer`, not `BigInt`
- Use the functions in util for conversions between numbers and strings
- Avoid C-style functions. Use classes with an `operator()` instead.
- Use `irep_idt` for identifiers (not `std::string`)
- Avoid destructive updates if possible. The `irept` has constant time copy.
- Use instances of `std::size_t` for comparison with return values of `.size()`
  of STL containers and algorithms, and use them as indices to arrays or
  vectors.
- Do not use default values in public functions
- Use assertions to detect programming errors, e.g. whenever you make
  assumptions on how your code is used
- Use exceptions only when the execution of the program has to abort because of
  erroneous user input
- We allow to use 3rd-party libraries directly. No wrapper matching the coding
  rules is required. Allowed libraries are: STL.
- When throwing, omit the brackets, i.e. `throw "error"`.
- Error messages should start with a lower case letter.
- Use the `auto` keyword if and only if one of the following
  - The type is explicitly repeated on the RHS (e.g. a constructor call)
  - Adding the type will increase confusion (e.g. iterators, function pointers)
- Avoid `assert`. If the condition is an actual invariant, use INVARIANT,
  PRECONDITION, POSTCONDITION, CHECK_RETURN, UNREACHABLE or DATA_INVARIANT (also
  see the documentation of the macros in `src/util/invariant.h`). If there are
  possible reasons why it might fail, throw an exception.
    - Use "should" style statements for messages in invariants (e.g. "array
      should have a non-zero size") to make both the violation and the expected
      behavior clear. (As opposed to "no zero size arrays" where it isn't clear
      if the zero-size array is the problem, or the lack of it).
    - The statements should start with a lower case letter.
- All raw pointers (such as those returned by `symbol_tablet::lookup`) are
  assumed to be non-owning, and should not be `delete`d. Raw pointers that
  point to heap-allocated memory should be private data members of an object
  which safely manages the pointer. As such, `new` should only be used in
  constructors, and `delete` in destructors. Never use `malloc` or `free`.

# CProver conventions
- Avoid if at all possible using irept methods like `get(ID_name)`, instead cast
  to a derived type (e.g. `class_typet`) and use the wrapper method `get_name`
- Use `can_cast_type`/`can_cast_expr` instead of directly checking the `id()`
  of an `irept`.

# Architecture-specific code
- Avoid if possible.
- Use `__LINUX__`, `__MACH__`, and `_WIN32` to distinguish the architectures.
- Don't include architecture-specific header files without `#ifdef` ...

# Output
- Do not output to `cout` or `cerr` directly (except in temporary debug code,
  and then guard `#include <iostream>` by `#ifdef DEBUG`)
- Derive from `messaget` if the class produces output and use the streams
  provided (`status()`, `error()`, `debug()`, etc)
- Use `\n` instead of `std::endl`

# Unit tests
- Unit tests are written using [Catch](https://github.com/philsquared/Catch)
- For large classes:
  - Create a separate file that contains the tests for each method of each
    class
  - The file should be named according to
    `unit/class/path/class_name/function_name.cpp`
- For small classes:
  - Create a separate file that contains the tests for all methods of each
    class
  - The file should be named according to `unit/class/path/class_name.cpp`
- Catch supports tagging, tests should be tagged with all the following tags:
  - [core] should be used for all tests unless the test takes more than 1
    second to run, then it should be tagged with [long]
  - [folder_name] of the file being tested
  - [class_name] of the class being tested
  - [function_name] of the function being tested

---

You are allowed to break rules if you have a good reason to do so.

---

# Pre-commit hook to run cpplint locally

To install the hook
```sh
cp .githooks/pre-commit .git/hooks/pre-commit
```
or use a symbolic link. Then, when running git commit, you should get the
linter output (if any) before being prompted to enter a commit message. To
bypass the check (e.g. if there was a false positive), add the option
`--no-verify`.

# CODE COVERAGE

Code coverage metrics are provided using gcov and lcov. Ensure that you have
installed lcov from http://ltp.sourceforge.net/coverage/lcov.php note for
ubuntu lcov is available in the standard apt-get repos.

To get coverage metrics run the following script from the regression directory:
```
get_coverage.sh
```
This will:
 1) Rebuild CBMC with gcov enabled
 2) Run all the regression tests
 3) Collate the coverage metrics
 4) Provide an HTML report of the current coverage

# USING CLANG-FORMAT

CBMC uses clang-format to ensure that the formatting of new patches is readable
and consistent. There are two main ways of running clang-format: remotely, and
locally.

## RUNNING CLANG-FORMAT REMOTELY

When patches are submitted to CBMC, they are automatically run through
continuous integration (CI). One of the CI checks will run clang-format over
the diff that your pull request introduces. If clang-format finds formatting
issues at this point, the build will be failed, and a patch will be produced
in the CI output that you can apply to your code so that it conforms to the
style guidelines.

To apply the patch, copy and paste it into a local file (`patch.txt`) and then
run:
```
patch -p1 -i patch.txt
```
Now, you can commit and push the formatting fixes.

## RUNNING CLANG-FORMAT LOCALLY

### INSTALLATION

To avoid waiting until you've made a PR to find formatting issues, you can
install clang-format locally and run it against your code as you are working.

Different versions of clang-format have slightly different behaviors. CBMC uses
clang-format-3.8 as it is available the repositories for Ubuntu 16.04 and
Homebrew.
To install on a Unix-like system, try installing using the system package
manager:
```
apt-get install clang-format-3.8  # Run this on Ubuntu, Debian etc.
brew install clang-format@3.8     # Run this on a Mac with Homebrew installed
```

If your platform doesn't have a package for clang-format, you can download a
pre-built binary, or compile clang-format yourself using the appropriate files
from the [LLVM Downloads page](http://releases.llvm.org/download.html).

An installer for Windows (along with a Visual Studio plugin) can be found at
the [LLVM Snapshot Builds page](http://llvm.org/builds/).

### FORMATTING A RANGE OF COMMITS

Clang-format is distributed with a driver script called git-clang-format-3.8.
This script can be used to format git diffs (rather than entire files).

After committing some code, it is recommended to run:
```
git-clang-format-3.8 upstream/develop
```
*Important:* If your branch is based on a branch other than `upstream/develop`,
use the name or checksum of that branch instead. It is strongly recommended to
rebase your work onto the tip of the branch it's based on before running
`git-clang-format` in this way.

### RETROACTIVELY FORMATTING INDIVIDUAL COMMITS

If your works spans several commits and you'd like to keep the formatting
correct in each individual commit, you can automatically rewrite the commits
with correct formatting.

The following command will stop at each commit in the range and run
clang-format on the diff at that point.  This rewrites git history, so it's
*unsafe*, and you should back up your branch before running this command:
```
git filter-branch --tree-filter 'git-clang-format-3.8 upstream/develop' \
  -- upstream/develop..HEAD
```
*Important*: `upstream/develop` should be changed in *both* places in the
command above if your work is based on a different branch. It is strongly
recommended to rebase your work onto the tip of the branch it's based on before
running `git-clang-format` in this way.
