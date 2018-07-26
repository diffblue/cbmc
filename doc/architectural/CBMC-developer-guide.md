\ingroup module_hidden 
\page cbmc-developer-guide CBMC Developer Guide

\author Martin Brain, Peter Schrammel, César Rodríguez, Owen Jones

\tableofcontents

\section section-compilation-and-development Compilation and Development

## Makefiles ##

First off, read the \ref cbmc-user-manual "CBMC User Manual". It describes
how to get, build and use CBMC. This document covers the
internals of the system and how to get started on development.

## CMake files ##

To be documented.

## Personal configuration: config.inc, macro DEBUG ##

To be documented.

## Generating doxygen documentation ##

Run `doxygen` in `/src`. HTML output will be created in `/doc/html`. The
index page is `/doc/html/index.html`.

Apart from the (user-orientated) CBMC user manual and this document, most
of the rest of the documentation is inline in the code as `doxygen` and
some comments. A man page for CBMC, goto-cc and goto-instrument is
contained in the `doc/` directory and gives some options for these
tools. All of these could be improved and patches are very welcome. In
some cases the algorithms used are described in the relevant papers.

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


\section section-background-concepts Background Concepts

## AST: types, globals, variables, functions, code blocks, language primitives, assignments, expressions, variables ##

To be documented.

## CFG ##

To be documented.

## Bounded model checking (from the CBMC manual) ##

To be documented.

### SSA ###

To be documented.

## SAT and SMT ##

To be documented.

## Static analysis ##

To be documented.


\section section-cprover-architecture CPROVER Architecture

This section provides a graphical overview of how CBMC fits together.
CBMC takes C code or a goto-binary as input and tries to emit traces
of executions that lead to crashes or undefined behaviour. The diagram
below shows the intermediate steps in this process.

\dot
digraph G {

  rankdir="TB";
  node [shape=box, fontcolor=blue];

  subgraph top {
    rank=same;
    1 -> 2 -> 3 -> 4;
  }

  subgraph bottom {
    rank=same;
    5 -> 6 -> 7 -> 8 -> 9;
  }

  /* shift bottom subgraph over */
  9 -> 1 [color=white];

  4 -> 5;

  1 [label="command line\nparsing" URL="\ref cbmc_parse_optionst"];
  2 [label="preprocessing,\nparsing" URL="\ref preprocessing"];
  3 [label="language\ntype-checking" URL="\ref type-checking"];
  4 [label="goto\nconversion" URL="\ref goto-conversion"];
  5 [label="instrumentation" URL="\ref instrumentation"];
  6 [label="symbolic\nexecution" URL="\ref symbolic-execution"];
  7 [label="SAT/SMT\nencoding" URL="\ref sat-smt-encoding"];
  8 [label="decision\nprocedure" URL="\ref decision-procedure"];
  9 [label="counter example\nproduction" URL="\ref counter-example-production"];
}
\enddot

The \ref cbmc-user-manual "CBMC User Manual" describes CBMC from a user
perspective. Each node in the diagram above links to the appropriate
class or module documentation, describing that particular stage in the
CBMC pipeline.
CPROVER is structured in a similar fashion to a compiler. It has
language specific front-ends which perform limited syntactic analysis
and then convert to an intermediate format. The intermediate format can
be output to files (this is what `goto-cc` does) and are (informally)
referred to as “goto binaries” or “goto programs”. The back-end are
tools process this format, either directly from the front-end or from
it’s saved output. These include a wide range of analysis and
transformation tools (see \ref section-other-tools).

# Concepts #
## {C, java bytecode} → Parse tree → Symbol table → GOTO programs → GOTO program transformations → BMC → counterexample (goto_tracet) → printing ##

To be documented.

## Instrumentation (for test gen & CBMC & ...): Goto functions -> goto functions ##

To be documented.

## Goto functions -> BMC -> Counterexample (trace) ##

To be documented.

## Trace -> interpreter -> memory map ##

To be documented.

## Goto functions -> abstract interpretation ##

To be documented.

## Executables (flow of transformations): ##

To be documented.

### goto-cc ###

To be documented.

### goto-instrument ###

To be documented.

### cbmc ###

To be documented.

### goto-analyzer ###

To be documented.


\section section-folder-walkthrough Folder walkthrough

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
  * \ref clobber
  * \ref goto-analyzer
  * \ref goto-instrument
  * \ref goto-diff
  * \ref memory-models
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

The `regression/` directory contains the test suites.
They are grouped into directories for each of the tools/modules.
Each of these contains a directory per test case, containing a C or C++
file that triggers the bug and a `.desc` file that describes
the tests, expected output and so on. There is a Perl script,
`test.pl` that is used to invoke the tests as:

    ../test.pl -c PATH_TO_CBMC

The `–help` option gives instructions for use and the
format of the description files.




\section section-data-structures-core-structures-and-ast Data structures: core structures and AST

## Strings: dstringt, the string_container and the ID_* ##
Within cbmc, strings are represented using `irep_idt`. By default this is
typedefed to \ref dstringt, which stores a string as an index into a large
static table of strings. This makes it easy to compare if two `irep_idt`s
are equal (just compare the index) and it makes it efficient to store
many copies of the same string. The static list of strings is initially populated
from `irep_ids.def`, so for example the fourth entry in `irep_ids.def` is
“IREP_ID_ONE(type)”, so the string “type” has index 3. You can refer to
this `irep_idt` as `ID_type`. The other kind of line you see is
“IREP_ID_TWO(C_source_location, #source_location)”, which means the
`irep_idt` for the string “#source_location” can be referred to as
`ID_C_source_location`. The “C” is for comment, which will be explained
in the next section. Any strings that need to be stored as `irep_id`s which
aren't in `irep_ids.def` are added to the end of the table when they are
first encountered, and the same index is used for all instances. 

See documentation at \ref dstringt.

## irept: a 4-triple (data, named-sub, comments, sub) ##
See documentation at \ref irept.

As that documentation says, `irept`s are generic tree nodes. You should
think of them as having a single string (data, actually an `irep_idt`) and
lots of child nodes, some of which are numbered (sub) and some of which are
labelled, and the label can either start with a “#” (comments-sub) or without
one (named-sub). The meaning of the “#” is that this child should not be
considered important, for example it shouldn’t be counted when comparing two
`irept`s for equality.

## typet ##

To be documented.

### symbol_typet ###

To be documented.

## exprt ##
\ref exprt is the class to represent an expression. It inherits from \ref irept,
and the only things it adds to it are that every \ref exprt has a named sub
containing its type and everything in the sub of an \ref exprt is again an
\ref exprt, not just an \ref irept. You can think of \ref exprt as a node in the
abstract syntax tree for an expression. There are many classes that
inherit from \ref exprt and which represent more specific things. For
example, there is \ref minus_exprt, which has a sub of size 2 (for the two
argument of minus).

Recall that every \ref irept has one piece of data of its own, i.e. its
`id()`, and all other information is in its `named_sub`, `comments` or
`sub`. For `exprt`s, the `id()` is used to specify why kind of \ref exprt this is,
so a \ref minus_exprt has `ID_minus` as its `id()`. This means that a
\ref minus_exprt can be passed wherever an \ref exprt is expected, and if you
want to check if the expression you are looking at is a minus
expression then you have to check its `id()` (or use
`can_cast_expr<minus_exprt>`).

## codet ##
\ref exprt represents expressions and \ref codet represents statements. \ref codet
inherits from \ref exprt, so all `codet`s are `exprt`s, with `id()` `ID_code`.
Many different kinds of statements inherit from \ref codet, and they are
distinguished by their `statement()`. For example, a while loop would be
represented by a \ref code_whilet, which has `statement()` `ID_while`.
\ref code_whilet has two operands in its sub, and helper functions to make
it easier to use: `cond()` returns the first subexpression, which
is the condition for the while loop, and `body()` returns the second
subexpression, which is the body of the while loop - this has to be
a \ref codet, because the body of a while loop is a statement.

## symbolt, symbol_table, and namespacet ##

To be documented.

### Symbol lifetimes, symbol modes, name, base-name, pretty-name; semantic of lifetimes for symex? ###

To be documented.

### Storing symbols and hiding symbols (namespacet) ###

To be documented.

### ns.follow ##

To be documented.


## Examples: how to represent the AST of statements, focus on java ##

To be documented.

### struct Array { int length, int *data }; ###

To be documented.

### x = y + 123 ###

To be documented.

### if (x > 10) { y = 2 } else { v[3] = 4 } ###

To be documented.



\section section-data-structures-from-ast-to-goto-program Data structures: from AST to GOTO program

## goto_programt ##

To be documented.

### The CFG of a function ###

To be documented.

### instructiont ###

See documentation at \ref instructiont.

#### Types, motivation of each type (dead?) #####

To be documented.

#### Accepted code (codet) values ####

To be documented.

#### Accepted guard (exprt) values ####

To be documented.

## goto_functionst ##

To be documented.

### A map from function names to function bodies (CFGs) ###

To be documented.

## goto_modelt ##

To be documented.

### A compilation unit ###

To be documented.

## Example: ##

To be documented.

### Unsigned mult (unsigned a, unsigned b) { int acc, i; for (i = 0; i < b; i++) acc += a; return acc; } ###

To be documented.




\section section-front-end-languages-generating-codet-from-multiple-languages Front-end languages: generating codet from multiple languages

## Front-end languages: generating codet from multiple languages ##

To be documented.

### language_uit, language_filest, languaget classes: ###

To be documented.

### Purpose ###

To be documented.

### Parse ###

To be documented.

### Typecheck ###

To be documented.

### Final ###

To be documented.

## Java bytecode: ##

To be documented.

### Explain how a java program / class is represented in a .class ###

To be documented.

### Explain the 2 step conversion from bytecode to codet; give an example with a class? ###

To be documented.



\section section-bmct-class Bmct class

## equation ##

To be documented.



\section section-symbolic-executors Symbolic executors

## Symex class ##

To be documented.



\section section-solvers-infrastructure Solvers infrastructure

## Flattening ##

To be documented.

## SMT solving API ##

To be documented.

## SAT solving API ##

To be documented.



\section section-static-analysis-apis Static analysis APIs


To be documented.



\section section-other-tools Other Tools

To be documented.: The text in this section is a bit outdated.

The CPROVER subversion archive contains a number of separate programs.
Others are developed separately as patches or separate
branches.Interfaces are have been and are continuing to stablise but
older code may require work to compile and function correctly.

In the main archive:

* `CBMC`:   A bounded model checking tool for C and C++. See 
  \ref cbmc.

* `goto-cc`:   A drop-in, flag compatible replacement for GCC and other
  compilers that produces goto-programs rather than executable binaries.
  See \ref goto-cc.

* `goto-instrument`:   A collection of functions for instrumenting and
  modifying goto-programs. See \ref goto-instrument.

Model checkers and similar tools:

* `SatABS`:   A CEGAR model checker using predicate abstraction. Is
  roughly 10,000 lines of code (on top of the CPROVER code base) and is
  developed in its own subversion archive. It uses an external model
  checker to find potentially feasible paths. Key limitations are
  related to code with pointers and there is scope for significant
  improvement.

* `Scratch`:   Alistair Donaldson’s k-induction based tool. The
  front-end is in the old project CVS and some of the functionality is
  in `goto-instrument`.

* `Wolverine`:   An implementation of Ken McMillan’s IMPACT algorithm
  for sequential programs. In the old project CVS.

* `C-Impact`:   An implementation of Ken McMillan’s IMPACT algorithm for
  parallel programs. In the old project CVS.

* `LoopFrog`:   A loop summarisation tool.

* `TAN`:   Christoph’s termination analyser.

Test case generation:

* `cover`:   A basic test-input generation tool. In the old
    project CVS.

* `FShell`:   A test-input generation tool that allows the user to
  specify the desired coverage using a custom language (which includes
  regular expressions over paths). It uses incremental SAT and is thus
  faster than the naïve “add assertions one at a time and use the
  counter-examples” approach. Is developed in its own subversion.

Alternative front-ends and input translators:

* `Scoot`:   A System-C to C translator. Probably in the old
    project CVS.

* `???`:   A Simulink to C translator. In the old project CVS.

* `???`:   A Verilog front-end. In the old project CVS.

* `???`:   A converter from Codewarrior project files to Makefiles. In
    the old project CVS.

Other tools:

* `ai`:   Leo’s hybrid abstract interpretation / CEGAR tool.

* `DeltaCheck?`:   Ajitha’s slicing tool, aimed at locating changes and
  differential verification. In the old project CVS.

There are tools based on the CPROVER framework from other research
groups which are not listed here.
