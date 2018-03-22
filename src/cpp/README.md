\ingroup module_hidden
\defgroup cpp cpp

# Folder cpp

\author Martin Brain

This directory contains the C++ front-end. It supports the subset of C++
commonly found in embedded and system applications. Consequentially it
doesn’t have full support for templates and many of the more advanced
and obscure C++ features. The subset of the language that can be handled
is being extended over time so bug reports of programs that cannot be
parsed are useful.

The functionality is very similar to the ANSI C front end; parsing the
code and converting to goto-programs. It makes use of code from
`langapi` and `ansi-c`.
