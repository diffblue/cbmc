\ingroup module_hidden
\defgroup util util

# Folder util

\author Martin Brain, Owen Jones

\section data_structures Data Structures

This section discusses some of the key data-structures used in the
CPROVER codebase.

\subsection irept_section Irept Data Structure

See \ref irept for more information.

\subsection irep_idt_section Irep_idt and Dstringt

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
