\ingroup module_hidden
\defgroup util util

# Folder util

\author Martin Brain, Owen Jones

\section data_structures Data Structures

\ref util contains some of the key data-structures used in the
CPROVER codebase.

\subsection irept_section irept: a 4-tuple (data, named-sub, comments, sub)

See documentation at \ref irept.

As that documentation says, [irept](\ref irept)s are generic tree nodes. You
should think of them as having a single string ([data](irept::data), actually
an \ref irep_idt) and lots of child nodes, some of which are numbered
([sub](\ref irept::dt::sub)) and some of which are labelled, and the label
can either start with a “\#” ([comments](\ref irept::dt::comments)) or without
one ([named_sub](\ref irept::dt::named_sub)). The meaning of the “\#” is that
this child should not be considered important, for example it shouldn't be
counted when comparing two [irept](\ref irept)s for equality.

\subsection irep_idt_section Strings: dstringt, the string_container and the ID_*

Within cbmc, strings are represented using \ref irep_idt, or \ref irep_namet
for keys to [named_sub](\ref irept::dt::named_sub) or
[comments](\ref irept::dt::comments). By default these are both
typedefed to \ref dstringt. For debugging purposes you can set `USE_STD_STRING`,
in which case they are both typedefed to `std::string`.

\ref dstringt stores a string as an index into a large
static table of strings. This makes it easy to compare if two
[irep_idt](\ref irep_idt)s are equal (just compare the index) and it makes it
efficient to store many copies of the same string. The static list of strings
is initially populated from `irep_ids.def`, so for example the fourth entry
in `irep_ids.def` is `“IREP_ID_ONE(type)”`, so the string “type” has index 3.
You can refer to this \ref irep_idt as `ID_type`. The other kind of line you
see is `“IREP_ID_TWO(C_source_location, #source_location)”`, which means the
\ref irep_idt for the string “#source_location” can be referred to as
`ID_C_source_location`. The “C” is for comment, meaning that it should be
stored in the ([comments](\ref irept::dt::comments). Any strings that need
to be stored as [irep_idt](\ref irep_idt)s which aren't in `irep_ids.def`
are added to the end of the table when they are first encountered, and the
same index is used for all instances.

See documentation at \ref dstringt.

\subsection typet_section typet

See \ref typet.

To be documented.

\subsubsection symbol_typet_section symbol_typet

See \ref symbol_typet.

To be documented.

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

To be documented.

\subsubsection symbol_lifetimes_section Symbol lifetimes, symbol modes, name, base-name, pretty-name; semantic of lifetimes for symex?

To be documented.

\subsubsection storing_symbols_section Storing symbols and hiding symbols (namespacet)

To be documented.

\subsubsection ns_follow_section ns.follow

To be documented.

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
