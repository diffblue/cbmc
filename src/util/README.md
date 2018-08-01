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

Inside \ref irept, strings are stored as irep_idts, or irep_namets for
keys to named_sub or comments. By default both irep_idt and irep_namet
are typedefed to \ref dstringt, unless USE_STD_STRING is set, in which
case they are typedefed to std::string (this can be used for debugging
purposes).

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
