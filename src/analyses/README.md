\ingroup module_hidden
\defgroup analyses analyses

# Folder analyses

This contains the abstract interpretation framework `ai.h` and several
static analyses that instantiate it.

\section analyses-frameworks Frameworks:

\subsection analyses-ait Abstract interpreter framework (ait)

To be documented.

\subsection analyses-static-analysist Old Abstract interpreter framework (static_analysist)

This is obsolete.

\subsection analyses-flow-insensitive-analysis Flow-insensitive analysis (flow_insensitive_analysist)

To be documented.

\section analyses-specific-analyses Specific analyses:

\subsection analyses-call-graph Call graph and associated helpers (call_grapht)

To be documented.

\subsection analyses-dominator Dominator analysis (cfg_dominators_templatet)

To be documented.

\subsection analyses-constant-propagation Constant propagation (constant_propagator_ait)

To be documented.

\subsection analyses-taint Taint analysis (custom_bitvector_analysist)

To be documented.

\subsection analyses-dependence-graph Data- and control-dependence analysis (dependence_grapht)

To be documented.

\subsection analyses-dirtyt Address-taken lvalue analysis (dirtyt)

To be documented.

\subsection analyses-const-cast-removal const_cast removal analysis (does_remove_constt)

To be documented.

\subsection analyses-escape Escape analysis (escape_analysist)

To be documented.

\subsection analyses-global-may-alias Global may-alias analysis (global_may_aliast)

To be documented.

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

To be documented.

\subsection analyses-reaching-definitions Reaching definitions (reaching_definitions_analysist)

To be documented.

\subsection analyses-uncaught-exceptions Uncaught exceptions analysis (uncaught_exceptions_domaint)

To be documented.

\subsection analyses-uninitialized-locals Uninitialized locals analysis (uninitialized_analysist)

To be documented.

\section analyses-transformations Transformations (arguably in the wrong directory):

\subsection analyses-goto-checkt Pointer / overflow / other check insertion (goto_checkt)

To be documented.

\subsection analyses-interval-analysist Integer interval analysis (interval_analysist) -- both an analysis and a transformation

To be documented.
