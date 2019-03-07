\ingroup module_hidden
\defgroup goto-checker goto-checker

# Folder goto-checker

\author Peter Schrammel

The \ref goto-checker directory contains interfaces for the verification of
goto-programs.

There are three main concepts:
* Property
* Goto Verifier
* Incremental Goto Checker

A property has a `property_id` and identifies an assertion that is either
part of the goto model or generated in the course of executing the verification
algorithm. A verification algorithm determines the `status` of a property,
i.e. whether the property has passed verification, failed, is yet to be
analyzed, etc. See \ref property_infot.

A goto verifier aims at determining and reporting
the status of all or some of the properties, _independently_ of the
actual verification algorithm (e.g. path-merging symbolic execution,
path-wise symbolic execution, abstract interpretation).
See \ref goto_verifiert.

An incremental goto checker is used by a goto verifier to execute the
verification algorithm. Incremental goto checkers keep the state of the
analysis and can be queried by the goto verifier repeatedly to return
their results incrementally. A query to an incremental goto checker
either returns when a violated property has been found or the
verification algorithm has terminated.  See \ref incremental_goto_checkert.
Incremental goto checkers can provide additional functionality by implementing
the respective interfaces:
* \ref goto_trace_providert : If a violated property has been
  found then a trace can be retrieved from the incremental goto checker.
* \ref fault_localization_providert : If a violated property has been
  found then a likely fault location can be determined.
* \ref witness_providert : A witness can be output (for violated
  and proved properties).

The combination of these three concepts enables:
* _Verification algorithms can be used interchangeably._
  There is a single, small interface for our verification engines.
* _Verification results reporting is uniform across all engines._
  Downstream tools can use the reporting output without knowing
  which verification algorithm was at work.
* _Building variants of verification engines becomes easy._
  Goto verifier and incremental goto checker implementations are built from
  small building blocks. It should therefore be easy to build variants
  by implementing these interfaces instead of hooking into a monolithic engine.
* _The code becomes easier to maintain._
  There are N things that do one thing each rather than one thing that does
  N things. New variants of verification algorithms can be added and removed
  without impacting others.

There are the following variants of goto verifiers at the moment:
* \ref stop_on_fail_verifiert : Checks all properties, but terminates
  as soon as the first violated property is found and reports this violation.
  A trace ends at a violated property. Witnesses are output.
* \ref all_properties_verifier_with_trace_storaget : Determines the status of
  all properties and outputs results when the verification algorithm has
  terminated. A trace ends at a violated property.
* \ref all_properties_verifiert : Determines the status of all properties and
  outputs verification results incrementally. In contrast to
  \ref all_properties_verifier_with_trace_storaget,
  \ref all_properties_verifiert does not require to store any traces.
  A trace ends at a violated property.
* \ref cover_goals_verifier_with_trace_storaget : Determines the status of
  all properties, but full traces with potentially several failing properties
  (e.g. coverage goals) are stored and results reported after the
  verification algorithm has terminated.
  The reporting uses 'goals' rather than 'property' terminology. I.e.
  a failing property means 'success' and a passing property 'failed'.
* \ref stop_on_fail_verifier_with_fault_localizationt : Same as
  \ref stop_on_fail_verifiert, but also finds and reports
  the most likely fault location. Requires an incremental goto checker
  that provides fault localization.
* \ref all_properties_verifier_with_fault_localizationt : Same as
  \ref all_properties_verifier_with_trace_storaget, but also finds and reports
  the most likely fault location. Requires an incremental goto checker
  that provides fault localization.

There are the following variants of incremental goto checkers at the moment:
* \ref multi_path_symex_checkert : The default mode of goto-symex. It explores
  all paths and applies aggressive path merging to generate a formula
  (aka 'equation') that is passed to the SAT/SMT solver. It supports
  determining the status of all properties, but not adding new properties
  after the first invocation. It provides traces, fault localization and witness
  output.
* \ref multi_path_symex_only_checkert : Same as \ref multi_path_symex_checkert,
  but does not call the SAT/SMT solver. It can only decide the status of
  properties by the simplifications that goto-symex performs.
* \ref single_path_symex_checkert : Activated with option `--paths`. It
  explores paths one by one and generates a formula (aka 'equation') for each
  path and passes it to the SAT/SMT solver. It supports
  determining the status of all properties, but not adding new properties
  after the first invocation. It provides traces and witness output.
* \ref single_path_symex_only_checkert : Same as
  \ref single_path_symex_checkert,
  but does not call the SAT/SMT solver. It can only decide the status of
  properties by the simplifications that goto-symex performs.
* There are variants for Java that perform a Java-specific preprocessing:
  \ref java_multi_path_symex_checkert,
  \ref java_multi_path_symex_only_checkert,
  \ref java_single_path_symex_checkert,
  \ref java_single_path_symex_only_checkert
