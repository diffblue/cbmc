\ingroup module_hidden
\defgroup module_goto-symex Symbolic Execution & Counterexample Production

\author Kareem Khazem

**Key classes:**
* goto_symex_statet
* goto_symext

\dot
digraph G {
	node [shape=box];
	rankdir="LR";
	1 [shape=none, label=""];
	2 [label="goto conversion"];
	3 [shape=none, label=""];
	1 -> 2 [label="goto-programs, goto-functions, symbol table"];
	2 -> 3 [label="equations"];
}
\enddot

---
\section counter-example-production Counter Example Production

In the \ref goto-symex directory.

**Key classes:**
* symex_target_equationt
* prop_convt
* \ref bmct
* fault_localizationt
* counterexample_beautificationt

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="goto conversion"];
  3 [shape=none, label=""];
  1 -> 2 [label="solutions"];
  2 -> 3 [label="counter-examples"];
}
\enddot
