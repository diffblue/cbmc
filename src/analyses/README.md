\ingroup module_hidden
\defgroup analyses analyses

# Folder analyses

This contains the abstract interpretation frameworks and several
static analyses that instantiate them.

\section analyses-frameworks Frameworks:

There are currently three abstract interpretation frameworks provided in this
directory. \ref analyses-ait, \ref analyses-flow-insensitive-analysis, and the
deprecated and obsolete \ref analyses-static-analysist.

\subsection analyses-ait Abstract interpreter framework (ait)

This abstract interpretation framework is the focus of current active
development, and is where most scalability improvements will happen.
It should be used as the basis for any new development work. This framework
is provided by \ref ait. This analysis framework is currently location sensitive
(meaning there is one abstract domain per code location) and is designed to be
run after the function pointer removal and return removal passes. There is
ongoing work to make this framework also support context sensitivity.

\subsection analyses-static-analysist Old Abstract interpreter framework (static_analysist)

The obsolete static analysis framework \ref static_analysist is only used by
\ref value_set_analysist. This abstract interpretation framework is deprecated in
favour of \ref analyses-ait, and should not be used as the basis for new code.
This framework is location sensitive (one domain per code location), but is able
to be run before function pointer removal and return removal phases.

\subsection analyses-flow-insensitive-analysis Flow-insensitive analysis (flow_insensitive_analysist)

Framework for flow-insensitive analyses. Maintains a single global abstract
value which instructions are invited to transform in turn. Unsound (terminates
too early) if
(a) there are two or more instructions that incrementally reach a fixed point,
for example by walking a chain of pointers and updating a points-to set, but
(b) those instructions are separated by instructions that don't update the
abstract value (for example, SKIP instructions). Therefore, not recommended for
new code.

Only current user in-tree is \ref value_set_analysis_fit and its close
relatives, \ref value_set_analysis_fivrt and \ref value_set_analysis_fivrnst

\section analyses-specific-analyses Specific analyses:

\subsection analyses-call-graph Call graph and associated helpers (call_grapht)

A [https://en.wikipedia.org/wiki/Call_graph](call graph) for a GOTO model or
GOTO functions collection. \ref call_grapht implements a basic call graph, but
can also export the graph in \ref grapht format, which permits more advanced
graph algorithms to be applied; see \ref call_graph_helpers.h for functions
that work with the \ref grapht representation.

\subsection analyses-dominator Dominator analysis (cfg_dominators_templatet)

To be documented.

\subsection analyses-constant-propagation Constant propagation (\ref constant_propagator_ait)

A simple, unsound constant propagator. Replaces RHS symbol expressions (variable
reads) with their values when they appear to have a unique value at a particular
program point. Unsound with respect to pointer operations on the left-hand side
of assignments.

\subsection analyses-taint Taint analysis (custom_bitvector_analysist)

To be documented.

\subsection analyses-dependence-graph Data- and control-dependence analysis (dependence_grapht)

To be documented.

\subsection analyses-dirtyt Address-taken lvalue analysis (dirtyt)

To be documented.

\subsection analyses-const-cast-removal const_cast removal analysis (does_remove_constt)

To be documented.

\subsection analyses-escape Escape analysis (escape_analysist)

This is a simple [https://en.wikipedia.org/wiki/Escape_analysis](escape analysis).
It is intended to implement `__CPROVER_cleanup` instructions, which say that a given
cleanup function should be run when a particular object goes out of scope. Examples of
its usage can be seen in `ansi-c/library/stdio.c` and `ansi-c/library/pthread_lib.c`,
where it is used to introduce assertions that a `FILE*` going out of scope has been
`fclose`'d or similarly that a `pthread_mutex*` has been properly destroyed.

For example `f = fopen("/tmp/hello", "wb"); __CPROVER_cleanup(f, check_closed);`
should result in a call to `check_closed(f)` or `check_closed()` (depending on
whether it has an argument) when `f` and all its aliases go out of scope.

The alias analysis is a simple union-find algorithm, and can introduce cleanup calls
too soon (i.e. before all aliases are really gone), so this overestimates the possible
problems caused by escaping pointers.

Note this differs from a typical escape analysis, which would conservatively
(over-)estimate the objects that may be reachable when (e.g.) a function exits;
this *underestimates* the reachable objects in order to favour false positives
over false negatives when testing for missing close operations.

\subsection analyses-global-may-alias Global may-alias analysis (global_may_aliast)

This is a pointer alias analysis (analysing the memory locations a pointer
expression may point to, and finding when two pointer expressions refer to 
the same storage locations). It is flow-insensitive, meaning that it computes
what memory locations pointer expressions may refer to at any time during the program
execution. It's called may-alias, because it looks for aliasing that may occur
during program execution (compared to analysis for aliasing that must occur). It's
an over-approximating analysis.

\subsection analyses-rwt Read-write range analysis (goto_rwt)

To be documented.

\subsection analyses-invariant-propagation Invariant propagation (invariant_propagationt)

To be documented.

\subsection analyses-is-threaded Multithreaded program detection (is_threadedt)

To be documented.

\subsection analyses-pointer-classification Pointer classification analysis (is-heap-pointer, might-be-null, etc -- local_bitvector_analysist)

To be documented.

\subsection analyses-cfg Control-flow graph (local_cfgt)

To be documented.

\subsection analyses-local-may-alias Local may-alias analysis (local_may_aliast)

To be documented.

\subsection analyses-safe-dereference Safe dereference analysis (local_safe_pointerst)

To be documented.

\subsection analyses-locals Address-taken locals analysis (localst)

To be documented.

\subsection analyses-natural-loop Natural loop analysis (natural_loops_templatet)

A natural loop is when the nodes and edges of a graph make one self-encapsulating
circle (implemented in /ref natural_loops_templatet) with no incoming edges from external nodes.
For example A -> B -> C -> D -> A is a natural loop, but if B has an incoming edge from X,
then it isn't a natural loop, because X is an external node. Outgoing edges don't affect
the natural-ness of a loop.

/ref cfg_dominators_templatet provides the dominator analysis used to determine if a nodes
children can only be reached through itself and is thus part of a natural loop, and whose specifics
is covered in a separate subsection.

A basic description for how a natural loop works is here: https://web.cs.wpi.edu/~kal/PLT/PLT8.6.4.html

\subsection analyses-reaching-definitions Reaching definitions (reaching_definitions_analysist)

To be documented.

\subsection analyses-uncaught-exceptions Uncaught exceptions analysis (uncaught_exceptions_domaint)

To be documented.

\subsection analyses-uninitialized-locals Uninitialized locals analysis (uninitialized_analysist)

To be documented.

\section analyses-transformations Transformations (arguably in the wrong directory):

\subsection analyses-goto-checkt Pointer / overflow / other check insertion (goto_checkt)

To be documented.

\subsection analyses-interval-analysis Integer interval analysis -- both an analysis and a transformation

\ref interval_analysis interprets instructions of the input \ref goto_modelt
over the \ref interval_domaint, evaluates variables for each program location
(as intervals) and instruments the program with assumptions representing the
over-approximation of variable values.
