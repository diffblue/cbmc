\ingroup module_hidden
\defgroup module_cbmc CBMC tour

\author Kareem Khazem

CBMC takes C code or a goto-binary as input and tries to emit traces of
executions that lead to crashes or undefined behaviour. The diagram
below shows the intermediate steps in this process.


\dot
digraph G {

  rankdir="TB";
  node [shape=box, fontcolor=blue];

  subgraph top {
    rank=same;
    1 -> 2 -> 3 -> 4;
  }

  subgraph bottom {
    rank=same;
    5 -> 6 -> 7 -> 8 -> 9;
  }

  /* shift bottom subgraph over */
  9 -> 1 [color=white];

  4 -> 5;

  1 [label="command line\nparsing" URL="\ref cbmc_parse_optionst"];
  2 [label="preprocessing,\nparsing" URL="\ref preprocessing"];
  3 [label="language\ntype-checking" URL="\ref type-checking"];
  4 [label="goto\nconversion" URL="\ref goto-conversion"];
  5 [label="instrumentation" URL="\ref instrumentation"];
  6 [label="symbolic\nexecution" URL="\ref symbolic-execution"];
  7 [label="SAT/SMT\nencoding" URL="\ref sat-smt-encoding"];
  8 [label="decision\nprocedure" URL="\ref decision-procedure"];
  9 [label="counter example\nproduction" URL="\ref counter-example-production"];
}
\enddot

The \ref cprover-manual "CProver Manual" describes CBMC from a user
perspective. Each node in the diagram above links to the appropriate
class or module documentation, describing that particular stage in the
CBMC pipeline.
