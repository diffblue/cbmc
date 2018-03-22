\ingroup module_hidden
\defgroup goto-instrument goto-instrument

# Folder goto-instrument

\author Martin Brain

The `goto-instrument/` directory contains a number of tools, one per
file, that are built into the `goto-instrument` program. All of them
take in a goto-program (produced by `goto-cc`) and either modify it or
perform some analysis. Examples include `nondet_static.cpp` which
initialises static variables to a non-deterministic value,
`nondet_volatile.cpp` which assigns a non-deterministic value to any
volatile variable before it is read and `weak_memory.h` which performs
the necessary transformations to reason about weak memory models. The
exception to the “one file for each piece of functionality” rule are the
program instrumentation options (mostly those given as “Safety checks”
in the `goto-instrument` help text) which are included in the
`goto-program/` directory. An example of this is
`goto-program/stack_depth.h` and the general rule seems to be that
transformations and instrumentation that `cbmc` uses should be in
`goto-program/`, others should be in `goto-instrument`.

`goto-instrument` is a very good template for new analysis tools. New
developers are advised to copy the directory, remove all files apart
from `main.*`, `parseoptions.*` and the `Makefile` and use these as the
skeleton of their application. The `doit()` method in `parseoptions.cpp`
is the preferred location for the top level control for the program.
