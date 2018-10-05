\ingroup module_hidden
\defgroup util util

# Folder util

\author Martin Brain, Owen Jones, Chris Smowton

\section util_data_structures Data Structures

\ref util contains some of the key data-structures used in the
CPROVER codebase.

\subsection irept_section irept: a general-purpose polymorphic tree

See detailed documentation at \ref irept.

[irept](\ref irept)s are generic tree nodes. You
should think of each node as holding a single string ([data](\ref irept::data),
actually an \ref irep_idt) and lots of child nodes, some of which are numbered
([sub](\ref irept::dt::sub)) and some of which are labelled, and the label
can either start with a “\#” ([comments](\ref irept::dt::comments)) or without
one ([named_sub](\ref irept::dt::named_sub)). The meaning of the “\#” is that
this child shouldn't be counted when comparing two [irept](\ref irept)s for
equality; this is usually used when making an advisory annotation which does
not alter the semantics of the program.

They are used to represent many kinds of structured objects throughout the
CPROVER codebase, such as expressions, types and code. An \ref exprt represents
expressions, including for example \ref equal_exprt, an equality predicate, or
\ref dereference_exprt, which represents the `*` unary dereference operator
found in C. A \ref typet represents a type, and may have other \ref typet nodes
as children: for example, \ref array_typet represents an array, and has a single
numbered child that gives the type of the array elements. Finally, \ref codet
represents imperative statements, such as \ref code_assignt, which represents an
imperative assignment. It has two numbered operands, its left- and right-hand
sides.

Note that \ref exprt, \ref codet and similar classes deriving from \ref irept
do so in order to add constraints to the general tree (for example, providing
accessor methods with user-friendly names, or enforcing invariants that a node
must have a certain number of children), but do not override virtual methods or
add fields.

The implementation of \ref irept allows saving memory by sharing instances of
its internal storage using a
[copy-on-write](https://en.wikipedia.org/wiki/Copy-on-write) scheme. For
example, the statement `irep1.sub()[0] = irep2;` will share rather than copy
`irep2` and its children, saving memory unless either irept is subsequently
modified, at which point a copy is made.

\subsection irept_discussion_section Discussion

Many other compiler infrastructures represent a polymorphic tree using nodes
specialised to a particular expression type: for example, perhaps a binary
addition operator could be represented using a tag plus two pointers to child
expressions, rather than allocating a whole irept (including a variable-length
expression vector and empty maps for storing named subexpressions). This may
save memory, but inhibits ad-hoc annotations such as tagging the addition
"does not overflow" without adding that field to addition operations globally
or maintaining a shadow data structure to track that information. This is easier
with a general irept structure that can store an arbitrary number of
arbitrarily-named child nodes.

Another optimisation commonly seen when storing polymorphic trees is to use a
uniform node data structure (like irept) but to keep the node compact, for
example storing at most four pointers and transparently allocating extension
nodes when necessary for an unusually large expression. This provides the best
of both worlds, obtaining compact storage for common cases such as unannotated
binary expressions while permitting deviation at times. The downside is that
implementing such a system is more complex than straightforwardly using C++
standard data structures as in irept.

\subsection irep_idt_section Strings: dstringt, the string_container and the ID_*

Within cbmc, strings are represented using \ref irep_idt, or \ref irep_namet
for keys to [named_sub](\ref irept::dt::named_sub) or
[comments](\ref irept::dt::comments). By default these are both
typedefed to \ref dstringt. For debugging purposes you can set `USE_STD_STRING`,
in which case they are both typedefed to `std::string`. You can also easily
convert an [irep_idt](\ref irep_idt) or [irep_namet](\ref irep_namet) to a
`std::string` using the [id2string](\ref id2string) or
[name2string](\ref name2string) function, respectively, or either of them to a
`char*` using the [c_str()](\ref dstringt::c_str) member function.

\ref dstringt stores a string as an index into a large
static table of strings. This makes it easy to compare if two
[irep_idt](\ref irep_idt)s are equal (just compare the index) and it makes it
efficient to store many copies of the same string. The static list of strings
is initially populated from `irep_ids.def`, so for example the fourth entry
in `irep_ids.def` is `“IREP_ID_ONE(type)”`, so the string “type” has index 3.
You can refer to this \ref irep_idt as `ID_type`. The other kind of line you
see is `“IREP_ID_TWO(C_source_location, #source_location)”`, which means the
\ref irep_idt for the string “\#source_location” can be referred to as
`ID_C_source_location`. The “C” is for comment, meaning that it should be
stored in the [comments](\ref irept::dt::comments). Any strings that need
to be stored as [irep_idt](\ref irep_idt)s which aren't in `irep_ids.def`
are added to the end of the table when they are first encountered, and the
same index is used for all instances.

See documentation at \ref dstringt.

\subsection typet_section typet

\ref typet represents the type of an expression. Types may have subtypes,
stored in two [sub](\ref irept::dt::sub)s named “subtype” (a single type) and
“subtypes” (a vector of types). For pre-defined types see `std_types.h` and
`mathematical_types.h`.

\subsubsection symbol_typet_section symbol_typet

\ref symbol_typet is a type used to store a reference to the symbol table. The
full \ref symbolt can be retrieved using the identifier of \ref symbol_typet.

\subsection exprt_section exprt

\ref exprt is the class to represent an expression. It inherits from \ref
irept, and the only things it adds to it are that (1) every \ref exprt has
an entry in [named_sub](\ref irept::dt::named_sub) containing its type and
(2) everything in the [sub](\ref irept::dt::sub) of an \ref exprt is again an
\ref exprt, not just an \ref irept. You can think of \ref exprt as a node in
the abstract syntax tree for an expression. There are many classes that
inherit from \ref exprt and which represent more specific things. For
example, there is \ref minus_exprt, which has a [sub](\ref irept::dt::sub)
of size 2 (for the two arguments of minus).

Recall that every \ref irept has one piece of data of its own, i.e. its
[id()](\ref irept::id()), and all other information is in its
[named_sub](\ref irept::dt::named_sub), [comments](\ref irept::dt::comments)
or [sub](\ref irept::dt::sub). For [exprt](\ref exprt)s, the
[id()](\ref irept::id()) is used to specify why kind of \ref exprt this is,
so a \ref minus_exprt has `ID_minus` as its [id()](\ref irept::id()). This
means that a \ref minus_exprt can be passed wherever an \ref exprt is
expected, and if you want to check if the expression you are looking at is
a minus expression then you have to check its [id()](\ref irept::id()) (or use
[can_cast_expr](\ref can_cast_expr)`<minus_exprt>`).

\subsection codet_section codet

See documentation at \ref codet.

\ref exprt represents expressions and \ref codet represents statements.
\ref codet inherits from \ref exprt, so all [codet](\ref codet)s are
[exprt](\ref exprt)s, with [id()](\ref irept::id()) `ID_code`.
Many different kinds of statements inherit from \ref codet, and they are
distinguished by their [statement](\ref codet::get_statement()). For example,
a while loop would be represented by a \ref code_whilet, which has
[statement](\ref codet::get_statement()) `ID_while`. \ref code_whilet has
two operands in its [sub](\ref irept::dt::sub), and helper functions to make
it easier to use: [cond()](\ref code_whilet::cond()) returns the first
subexpression, which is the condition for the while loop, and
[body()](\ref code_whilet::body()) returns the second subexpression, which
is the body of the while loop - this has to be a \ref codet, because the body
of a while loop is a statement.

\subsection symbolt_section symbolt, symbol_tablet, and namespacet

A symbol table is a mapping from symbol names to \ref symbolt objects, which
store a symbol's name, attributes, type and perhaps value. They are used to
describe local and global variables, type definitions and function prototypes
and definitions.

All symbols store a type (an instance of \ref typet). For function or method
symbols these are \ref code_typet instances.

Global variable symbols may have a value (an \ref exprt), in which case it is
used to initialise the global.

Method or function symbols may also have a value, in which case it is a
\ref codet and gives the function definition. A method or function symbol
without a value is a prototype (for example, it might be an `extern` declaration
in C). A function symbol that has been converted to a GOTO function *may* be
replaced with a special "compiled" value, but this varies from driver program to
program -- at the time of writing, only \ref goto-cc does this.

Local variables' symbol values are always ignored;
any initialiser must be explicitly assigned after they are instantiated by a
declaration (\ref code_declt).

Symbol expressions (\ref symbol_exprt) and types (\ref symbol_typet) refer to
symbols stored in a symbol table. Symbol expressions can be thought of as
referring to the table for more detail about a symbol (for example, is it a
local or a global variable, or perhaps a function?), and have a type which must
match the type given in the symbol table. Symbol types can be thought of as
shorthands or aliases for a type given in more detail in the symbol table, for
example permitting a shorthand for a large structure type, as well as permitting
the construction of expressions referring to that type before its full
definition is known.

Note the implementation of \ref symbol_tablet is split into a base interface
(\ref symbol_table_baset) and an implementation (\ref symbol_tablet). There is
one alternate implementation (\ref journalling_symbol_tablet) which additionally
maintains a log or journal of symbol creation, modification and deletions.

Namespaces (\ref namespacet) provide a read-only view on one or more symbol
tables, and provide helper functions that aid accessing the table. A namespace
may layer one or more symbol tables, in which case any lookup operation checks
the 'top' symbol table before moving down the layers towards the 'bottom' symbol
table, looking up the target symbol name in each successive table until one is
found. Note class \ref multi_namespacet can layer arbitrary numbers of symbol
tables, while for historical reasons \ref namespacet can layer up to two.

The namespace wrapper class also provides the \ref namespacet::follow
operation, which dereferences a `symbol_typet` to retrieve the type it refers
to, including following a symbol_typet which refers to another symbol which
eventually refers to a 'real' type.

\subsubsection symbolt_lifetime Symbol lifetimes

Symbols with \ref symbolt::is_static_lifetime set are initialised before a
program's entry-point is called and live until it ends. Such long-lived
variables are used to implement globals, but also C's procedure-local static
variables, which have restricted visiblity but the lifetime of a global.
They may be marked dead using a \ref code_deadt instruction, but this does not
render the variable inaccessible, it only indicates that the variable's current
value will not be read without an intervening write.

Non-type, non-global symbols (those with \ref symbolt::is_static_lifetime and
\ref symbolt::is_type not set) are local variables, and their lifespan
description varies depending on context.

In symbol table function definitions (the values of function-typed symbols),
local variables are created using a \ref code_declt instruction, and live until
their enclosing \ref code_blockt ends (similar to the C idiom
`{ int x; ... } // x lifespan ends`). By contrast in GOTO programs locals are
declared using a DECL instruction and live until a DEAD instruction referring
to the same symbol. Explicit DEAD instructions are always used rather than
killing implicitly by exiting a function.

Multiple instances of the same local may be live at the same time by virtue of
recursive function calls; a dead instruction or scope end always targets the
most recently allocated instance.

Scoping rules are particular to source languages and are not enforced by
CPROVER. For example, in standard C it is not possible to refer to a local
variable across functions without using a pointer, but in some possible source
languages this is permitted.

\subsubsection symbolt_details Symbol details

Symbols have:
* A mode, which indicates the source language frontend responsible for creating
  them. This is mainly used in pretty-printing the symbol table, to indicate
  the appropriate language frontend to use rendering the symbol's value and/or
  type. For example, mode == ID_C == "C" indicates that \ref ansi_ct, the C
  front-end, should be used to pretty-print, which in turn delegates to
  \ref expr2ct.
* A base-name and pretty-name, which are a short and user-friendly version of
  the symbol's definitive name respectively.
* Several flags (see \ref symbolt for full details), including
  \ref symbolt::is_static_lifetime (is this a global variable symbol?),
  \ref symbolt::is_type (is this a type definition),
  \ref symbolt::is_thread_local (of a variable, are there implicitly instances
    of this variable per-thread?).

\subsection cmdlinet

See \ref cmdlinet.

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

\subsection ast-examples-section Examples: how to represent the AST of statements, in C and in java

\subsubsection ast-example-1-section x = y + 123

To be documented..

\subsubsection ast-example-2-section if (x > 10) { y = 2 } else { v[3] = 4 }

To be documented.

\subsubsection ast-example-3-section Java arrays: struct Array { int length, int *data };

To be documented.

\subsection section-goto-typecheck Goto Model Typecheck

Class `typecheckt`.

\subsection irep-serialization `irept` Serialization

The module provides serialisation and deserialisation of
integer numbers, strings, and `irept` instances.

This is implemented in C++ modules:
  - `irep_serialization.h`
  - `irep_serialization.cpp`
  - `irep_hash_container.h` (applies only to `irept` instances)
  - `irep_hash_container.cpp` (applies only to `irept` instances)

\subsubsection irep-serialization-numbers Serialization of Numbers

A number is serialiased in 7-bit encoding. For example, given a 2-byte
number in base 2, like `10101010 01010101`, then it is saves in 3 bytes,
where each byte takes only 7 bits from the number, reading from the
left. The 8th bit in each output byte is set to 1 except in the last
byte, where the bit is 0. That 0 bit indicates the end of the
encoding of the number. So, the output bytes look like this:
`11010101 11010100 00000010`.

This is implmented in the function `::write_gb_word`.

The deserialisation does the oposite process and it is implemented in
`irep_serializationt::read_gb_word`.

\subsubsection irep-serialization-strings Serialization of Strings

A string is encoded as classic 0-terminated C string. However,
characters `0` and `\\` are escaped by writing additional `\\` 
before them. 

This is implmented in the function `::write_gb_string` and the
deserialisation is implemented in `irep_serializationt::read_gb_string`.

Each string which is stored inside an `::irept` instance is saved (meaining
its characters) into the ouptut stream, only in the first serialisation
query of the string. In that case, before the string there is also saved
a computed integer hash code of the string. Then, all subsequent
serialisation queries save only that integer hash code of the string.

\subsubsection irep-serialization-ireps Serialization of `irept` Instances

