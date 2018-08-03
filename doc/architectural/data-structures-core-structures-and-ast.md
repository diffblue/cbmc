\ingroup module_hidden 
\page data-structures-core-structures-and-ast Data structures: core structures and AST

\author Martin Brain, Peter Schrammel, Owen Jones

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
