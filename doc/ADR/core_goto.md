\page core-goto Core goto definition

During the analysis of a program CBMC transforms the input program in an intermediate language
called extended goto. Then the tool performs a series of simplifications on the obtained goto
program until the program is given to the solver.

We say that a program is in the **core goto form** when all the extended goto features have
been simplified.

More specifically, a program that is in **core goto form** is one that can be passed to **symex** by
using any solver deriving from `goto_verifiert` without requiring any lowering step.

At the time of writing, verifiers extending `goto_verifiert` are:

* `all_properties_verifier_with_fault_localizationt`,
* `all_properties_verifier_with_trace_storaget`,
* `all_properties_verifiert`,
* `cover_goals_verifier_with_trace_storaget`,
* `stop_on_fail_verifier_with_fault_localizationt`,
* `stop_on_fail_verifiert`.
