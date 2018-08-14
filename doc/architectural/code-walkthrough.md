\ingroup module_hidden 
\page code-walkthrough Code Walkthrough

\author Cesar Rodriguez, Owen Jones

testing

\section data-structures-core-structures-and-ast-section Data structures: core structures and AST

The core structures used for representing abstract syntax trees are all
documented in \ref util.

\subsection ast-examples-section Examples: how to represent the AST of statements, in C and in java

\subsubsection ast-example-1-section x = y + 123

To be documented..

\subsubsection ast-example-2-section if (x > 10) { y = 2 } else { v[3] = 4 }

To be documented.

\subsubsection ast-example-3-section Java arrays: struct Array { int length, int *data };

To be documented.


\section data-structures-from-ast-to-goto-program-section Data structures: from AST to GOTO program

\subsection goto-programt-section goto_programt

See \ref goto-programs, \ref goto_programt and [instructiont](\ref goto_programt::instructiont).

\subsection goto-program-example-section Example:

\subsubsection goto-program-example-1-section Unsigned mult (unsigned a, unsigned b) { int acc, i; for (i = 0; i < b; i++) acc += a; return acc; }

To be documented.


\section front-end-languages-generating-codet-from-multiple-languages-section Front-end languages: generating codet from multiple languages

\subsection language-uit-section language_uit, language_filest, languaget classes:

See \ref langapi.

\subsubsection parse-section Parse

See \ref language_uit::parse().

\subsubsection typecheck-section Typecheck

See \ref language_uit::typecheck().

\subsubsection final-section Final

See \ref language_uit::final().

\subsection languages-c-section C

See \ref ansi-c.

\subsection languages-cpp-section C++

See \ref cpp.

\subsection languages-java-section Java bytecode

See \ref java_bytecode.

\subsubsection java-class-section Explain how a java program / class is represented in a .class

To be documented.

\subsubsection java-bytecode-conversion-section Explain the 2 step conversion from bytecode to codet

To be documented.

\subsubsection java-bytecode-conversion-example-section A worked example of converting java bytecode to codet

To be documented.


\section bmct-class-section Bmct class

\subsection equation-section equation

See \ref symex-overview.


\section symbolic-executors-section Symbolic executors

\subsection symbolic-execution-section Symbolic execution

See \ref symex-overview.


\section solvers-infrastructure-section Solvers infrastructure

See \ref solvers-overview.

\subsection flattening-section Flattening

To be documented.

\subsection smt-solving-api-section SMT solving API

To be documented.

\subsection sat-solving-api-section SAT solving API

To be documented.


\section  static-analysis-apis-section Static analysis APIs

See \ref analyses and \ref pointer-analysis.
