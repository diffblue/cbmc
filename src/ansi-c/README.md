\ingroup module_hidden
\defgroup ansi-c ansi-c
# Folder ansi-c

\author Kareem Khazem, Martin Brain

\section overview Overview

Contains the front-end for ANSI C, plus a variety of common extensions.
This parses the file, performs some basic sanity checks (this is one
area in which the UI could be improved; patches most welcome) and then
produces a goto-program (see below). The parser is a traditional Flex /
Bison system.

`internal_addition.c` contains the implementation of various ‘magic’
functions that are that allow control of the analysis from the source
code level. These include assertions, assumptions, atomic blocks, memory
fences and rounding modes.

The `library/` subdirectory contains versions of some of the C standard
header files that make use of the CPROVER built-in functions. This
allows CPROVER programs to be ‘aware’ of the functionality and model it
correctly. Examples include `stdio.c`, `string.c`, `setjmp.c` and
various threading interfaces.

\section preprocessing Preprocessing & Parsing

In the \ref ansi-c directory

**Key classes:**
* \ref languaget and its subclasses
* ansi_c_parse_treet

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="preprocessing & parsing"];
  3 [shape=none, label=""];
  1 -> 2 [label="Command line options, file names"];
  2 -> 3 [label="Parse tree"];
}
\enddot


\section type-checking Type-checking

In the \ref ansi-c directory

**Key classes:**
* \ref languaget and its subclasses
* \ref irept
* \ref irep_idt
* \ref symbolt
* symbol_tablet

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="type checking"];
  3 [shape=none, label=""];
  1 -> 2 [label="Parse tree"];
  2 -> 3 [label="Symbol table"];
}
\enddot

This stage generates a symbol table, mapping identifiers to symbols;
\ref symbolt "symbols" are tuples of (value, type, location, flags).

This is a good point to introduce the \ref irept ("internal
representation") class---the base type of many of CBMC's hierarchical
data structures. In particular, \ref exprt "expressions",
\ref typet "types" and \ref codet "statements" are all subtypes of
\ref irept.
An irep is a tree of ireps. A subtlety is that an irep is actually the
root of _three_ (possibly empty) trees, i.e. it has three disjoint sets
of children: \ref irept::get_sub() returns a list of children, and
\ref irept::get_named_sub() returns an association from names to children.
**Most clients never use these functions directly**,
as subtypes of irept generally provide more
descriptive functions. For example, the operands of an
\ref exprt "expression" (\ref exprt::op0() "op0", op1 etc) are
really that expression's children; the
\ref code_assignt::lhs() "left-hand" and right-hand side of an
\ref code_assignt "assignment" are the children of that assignment.
The \ref irept::pretty() function provides a descriptive string
representation of an irep.

\ref irep_idt "irep_idts" ("identifiers") are strings that use sharing
to improve memory consumption. A common pattern is a map from irep_idts
to ireps. A goto-program contains a single symbol table (with a single
scope), meaning that the names of identifiers in the target program are
lightly mangled in order to make them globally unique. If there is an
identifier `foo` in the target program, the `name` field of `foo`'s
\ref symbolt "symbol" in the goto-program will be
* `foo` if it is global;
* <code>bar\::foo</code> if it is a parameter to a function `bar()`;
* <code>bar\::3\::foo</code> if it is a local variable in a function
  `bar()`, where `3` is a counter that is incremented every time a
  newly-scoped `foo` is encountered in that function.

The use of *sharing* to save memory is a pervasive design decision in
the implementation of ireps and identifiers. Sharing makes equality
comparisons fast (as there is no need to traverse entire trees), and
this is especially important given the large number of map lookups
throughout the codebase. More importantly, the use of sharing saves vast
amounts of memory, as there is plenty of duplication within the
goto-program data structures. For example, every statement, and every
sub-expression of a statement, contains a \ref source_locationt
that indicates the source file and location that it came from. Every
symbol in every expression has a field indicating its type and location;
etc. Although each of these are constructed as separate objects, the
values that they eventually point to are shared throughout the codebase,
decreasing memory consumption dramatically.

The Type Checking stage turns a parse tree into a
\ref symbol_tablet "symbol table". In this context, the 'symbols'
consist of code statements as well as what might more traditionally be
called symbols. Thus, for example:
* The statement `int foo = 11;` is converted into a symbol whose type is
  integer_typet and value is the \ref constant_exprt
  "constant expression" `11`; that symbol is stored in the symbol table
  using the mangled name of `foo` as the key;
* The function definition `void foo(){ int x = 11; bar(); }` is
  converted into a symbol whose type is \ref code_typet (not to be
  confused with \ref typet or \ref codet!); the code_typet contains the
  parameter and return types of the function. The value of the symbol is
  the function's body (a \ref codet), and the symbol is stored in the
  symbol table with `foo` as the key.


\section performance Parsing performance considerations

* Measured on trunk/regression/ansi-c/windows_h_VS_2012/main.i

* 13%: Copying into i_preprocessed

* 5%: ansi_c_parser.read()

* 53%: yyansi_clex()

* 29%: parser (without typechecking)

\section references Compiler References

CodeWarrior C Compilers Reference 3.2:

http://cache.freescale.com/files/soft_dev_tools/doc/ref_manual/CCOMPILERRM.pdf

http://cache.freescale.com/files/soft_dev_tools/doc/ref_manual/ASMX86RM.pdf

ARM 4.1 Compiler Reference:

http://infocenter.arm.com/help/topic/com.arm.doc.dui0491c/DUI0491C_arm_compiler_reference.pdf
