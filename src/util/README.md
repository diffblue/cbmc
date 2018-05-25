\ingroup module_hidden
\defgroup util util

# Folder util

\author Martin Brain, Owen Jones

\section data_structures Data Structures

This section discusses some of the key data-structures used in the
CPROVER codebase.

\subsection irept Irept Data Structure

There are a large number of kinds of tree structured or tree-like data in
CPROVER. `irept` provides a single, unified representation for all of
these, allowing structure sharing and reference counting of data. As
such `irept` is the basic unit of data in CPROVER.  Each `irept`
contains[^1] a basic unit of data (of type `dt`) which contains four
things:

* `data`:   A string[^2], which is returned when the `id()` function is
  used.

* `named_sub`:   A map from `irep_namet` (a string) to `irept`. This
  is used for named children, i.e.  subexpressions, parameters, etc.

* `comments`:   Another map from `irep_namet` to `irept` which is used
  for annotations and other ‘non-semantic’ information

* `sub`:   A vector of `irept` which is used to store ordered but
  unnamed children.

The `irept::pretty` function outputs the contents of an `irept` directly
and can be used to understand and debug problems with `irept`s.

On their own `irept`s do not “mean” anything; they are effectively
generic tree nodes. Their interpretation depends on the contents of
result of the `id` function (the `data`) field. `util/irep_ids.txt`
contains the complete list of `id` values. During the build process it
is used to generate `util/irep_ids.h` which gives constants for each id
(named `ID_`). These can then be used to identify what kind of data
`irept` stores and thus what can be done with it.

To simplify this process, there are a variety of classes that inherit
from `irept`, roughly corresponding to the ids listed (i.e.  `ID_or`
(the string `"or”`) corresponds to the class `or_exprt`). These give
semantically relevant accessor functions for the data; effectively
different APIs for the same underlying data structure. None of these
classes add fields (only methods) and so static casting can be used. The
inheritance graph of the subclasses of `irept` is a useful starting
point for working out how to manipulate data.

There are three main groups of classes (or APIs); those derived from
`typet`, `codet` and `exprt` respectively. Although all of these inherit
from `irept`, these are the most abstract level that code should handle
data. If code is manipulating plain `irept`s then something is wrong
with the architecture of the code.

Many of the key descendent of `exprt` are declared in `std_expr.h`. All
expressions have a named subfield / annotation which gives the type of
the expression (slightly simplified from C/C++ as `unsignedbv_typet`,
`signedbv_typet`, `floatbv_typet`, etc.). All type conversions are
explicit with an expression with `id() == ID_typecast` and an ‘interface
class’ named `typecast_exprt`. One key descendent of `exprt` is
`symbol_exprt` which creates `irept` instances with the id of “symbol”.
These are used to represent variables; the name of which can be found
using the `get_identifier` accessor function.

`codet` inherits from `exprt` and is defined in `std_code.h`. It
represents executable code; statements in C rather than expressions. In
the front-end there are versions of these that hold whole code blocks,
but in goto-programs these have been flattened so that each `irept`
represents one sequence point (almost one line of code / one
semi-colon). The most common descendents of `codet` are `code_assignt`
so a common pattern is to cast the `codet` to an assignment and then
recurse on the expression on either side.

[^1]: Or references, if reference counted data sharing is enabled. It is
    enabled by default; see the `SHARING` macro.

[^2]: Unless `USE_STD_STRING` is set, this is actually
a `dstring` and thus an integer which is a reference into a string table

\subsection irep_idt Irep_idt and Dstringt

Inside `irept`s, strings are stored as `irep_idt`s, or `irep_namet`s for
keys to `named_sub` or `comments`. If `USE_STD_STRING` is set then both 
`irep_idt` and `irep_namet` are `typedef`ed to `std::string`, but by default 
it is not set and they are `typedef`ed to `dstringt`. `dstringt` has one 
field, an unsigned integer which is an index into a static table of strings. 
This makes it expensive to create a new string (because you have to look 
through the whole table to see if it is already there, and add it if it 
isn't) but very cheap to compare strings (just compare the two integers). It 
also means that when you have lots of copies of the same string you only have
to store the whole string once, which saves space.

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="command line parsing"];
  3 [shape=none, label=""];
  1 -> 2 [label="C files or goto-binaries"];
  2 -> 3 [label="Command line options, file names"];
}
\enddot
