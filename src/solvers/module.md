\ingroup module_hidden
\defgroup module_solvers SAT/SMT Encoding and Decision Procedure

\author Kareem Khazem

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
