\ingroup module_hidden
\defgroup module_solvers SAT/SMT Encoding and Decision Procedure

\author Kareem Khazem

The basic role of solvers is to answer whether the set of equations given
is satisfiable.
One example usage, is to determine whether an assertion in a
program can be violated.
We refer to \ref module_goto-symex for how CBMC and JBMC convert a input program
and property to a set of equations.

The secondary role of solvers is to provide a satisfying assignment of
the variables of the equations, this can for instance be used to construct
a trace.

The most general solver in terms of supported equations is \ref string-solver.

\section sat-smt-encoding SAT/SMT Encoding

In the \ref solvers directory.

**Key classes:**
* \ref literalt
* \ref boolbvt
* \ref propt

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="equations"];
	2 -> 3 [label="propositional variables as bitvectors, constraints"];
}
\enddot


---

\section decision-procedure Decision Procedure

In the \ref solvers directory.

**Key classes:**
* symex_target_equationt
* \ref propt
* \ref bmct

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="propositional variables as bitvectors, constraints"];
	2 -> 3 [label="solutions"];
}
\enddot
