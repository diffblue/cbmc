# CBMC Feature Ideas

The following are features that would be good to add to CBMC. They are
listed here to gather information on them and also as a starting point
for contributors who are interested in undertaking a more comprehensive
project.

## Refinement-Based Slicing

**Task**: Implement refinement-based slicing to improve the slicing
of CBMC.

**Background**:
Some patches have been considered for this, but there is not yet
evidence of performance improvement. See
https://github.com/diffblue/cbmc/issues/28

## Refinement-based reduction of partial order constraints

**Task**: Implement refinement-based reduction of partial order
constraints.

**Background**:
Some patches have been considered for this, but there needs to also be
work on the performance. See
https://github.com/diffblue/cbmc/issues/29


## Advanced goto-diff

**Task**: Improve the goto-diff utility to have both syntactic and
semantic diff options for goto programs.

**Background**: The current `goto-diff` program performs only syntatic
diff of goto programs. Extensions to also consider semantic differences
would be desirable. It would be nice to include:
* deltacheck's change impact analysis
* cemc equivalence checker

See also https://github.com/diffblue/cbmc/issues/40

## Function Summaries

**Task**: Create function summaries that simplify analysis. The main
goals of the function summaries are:
* context insensitivity (there is one summary applicable in any
context the function is called from)
* transitive closure (effects of all callees are captured in summaries
of the root caller function)
* generalised interface (suitable for many different concrete
summary-computing algorithms)
* language independent (should work for Java, C, C++, ...)

This also has links to other projects (albeit some may be out of date
at this stage):
* test_gen (our summaries should fit to needs of this tests generation
task)
* 2ls (their summaries should also be expressible in our summaries)
* path-symex (summaries must also be usable for path-based symbolic
execution)

There are also complexities related to over/under-approximation
for the function summaries. For more details see
https://github.com/diffblue/cbmc/issues/218


## --cover array

**Task**: Extend the `--cover` option to add coverage goals for each
possible entry of fixed size arrays. For more details see
https://github.com/diffblue/cbmc/issues/265

