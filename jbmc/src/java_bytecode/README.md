\ingroup module_hidden
\defgroup java_bytecode java_bytecode

This module provides a front end for Java.

\section java-bytecode-conversion-section Overview of conversion from bytecode to codet

To be documented.

\section java-bytecode-object-factory Object Factory

To be documented.

\subsection java-bytecode-pointer-type-selection Pointer type selection

To be documented.

\subsection java-bytecode-genereic-substitution Generic substitution

To be documented.

\section java-bytecode-parsing Java bytecode parsing (parser, convert_class, convert_method)

To be documented.

\subsection java-class-section How a java program / class is represented in a .class

To be documented.

\section java-bytecode-runtime-exceptions Adding runtime exceptions (java_bytecode_instrument)

To be documented.

\section java-bytecode-concurrency-instrumentation Concurrency instrumentation

To be documented.

\section java-bytecode-remove-java-new Remove java new

To be documented.

\section java-bytecode-remove-exceptions remove_exceptions

To be documented.

\section java-bytecode-remove-instanceof Remove instanceof

\ref remove_instanceof.h removes the bytecode instruction `instanceof ` and replaces it with two instructions:
 - check whether the pointer is null
 - if not null, does the class identifier match the type of any of its subtypes

\section java-bytecode-method-stubbing Method stubbing

To be documented.

\section java-bytecode-lazy-methods-v1 Context Insensitive lazy methods (aka lazy methods v1)

To be documented.

\section java-bytecode-core-models-library Core Models Library

To be documented.

\section java-bytecode-java-types java_types

To be documented.

\section java-bytecode-string-library String library

To be documented.

See also \ref string-solver-interface.

\section java-bytecode-conversion-example-section A worked example of converting java bytecode to codet

To be documented.
