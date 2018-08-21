\ingroup module_hidden
\defgroup pointer-analysis pointer-analysis

# Folder pointer-analysis

\author Martin Brain

To perform symbolic execution on programs with dereferencing of
arbitrary pointers, some alias analysis is needed.  `pointer-analysis`
contains the three levels of analysis; flow and context insensitive,
context sensitive and flow and context sensitive. The code needed is
subtle and sophisticated and thus there may be bugs.

\section pointer-analysis-utilities Utilities:

\subsection pointer-analysis-object-numbering Object / expression numbering (object_numberingt)

To be documented.

\subsection pointer-analysis-pointer-offset-sum Pointer-offset sum (pointer_offset_sum)

To be documented.

\subsection pointer-analysis-rewrite-index Rewrite index (x[i] -> *(x+i)) (rewrite_index)

To be documented.

\section pointer-analysis-analysis Value-set Analysis:

To be documented.

\subsection pointer-analysis-variants Variants:

\subsubsection pointer-analysis-flow-insensitive Flow-insensitive

To be documented.

\subsubsection pointer-analysis-flow-insensitive-with-vr Flow-insensitive with 'vr' (value reduction?)

To be documented.

\subsubsection pointer-analysis-flow-insensitive-with-vr-ns Flow-insensitive with 'vr' and 'ns' (value reduction, ???)

To be documented.

\section pointer-analysis-transformations Transformations:

\subsection pointer-analysis-add-failed-symbols

This is obsolete.

\subsection pointer-analysis-dereference-removal Dereference removal (*x -> x == &o1 ? o1 : ...) -- dereferencet, dereference_callbackt, value_set_dereferencet, goto_program_dereferencet, etc

To be documented.
