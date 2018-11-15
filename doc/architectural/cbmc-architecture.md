\ingroup module_hidden
\page cbmc-architecture CBMC Architecture

\author Martin Brain, Peter Schrammel

This section provides a graphical overview of how CBMC fits together.
CBMC takes C code or a goto-binary as input and tries to emit traces
of executions that lead to crashes or undefined behaviour. The diagram
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
  5 [label="instrumentation" URL="\ref section-goto-transforms"];
  6 [label="symbolic\nexecution" URL="\ref symbolic-execution"];
  7 [label="SAT/SMT\nencoding" URL="\ref sat-smt-encoding"];
  8 [label="decision\nprocedure" URL="\ref decision-procedure"];
  9 [label="counter example\nproduction" URL="\ref counter-example-production"];
}
\enddot

The [CPROVER User Manual](http://www.cprover.org/cprover-manual/) describes
CBMC from a user perspective. Each node in the diagram above links to the
appropriate class or module documentation, describing that particular stage
in the CBMC pipeline.
CPROVER is structured in a similar fashion to a compiler. It has
language specific front-ends which perform limited syntactic analysis
and then convert to an intermediate format. The intermediate format can
be output to files (this is what `goto-cc` does) and are (informally)
referred to as “goto binaries” or “goto programs”. The back-end are
tools process this format, either directly from the front-end or from
it’s saved output. These include a wide range of analysis and
transformation tools (see \ref other-tools).

# Concepts #
## {C, java bytecode} &rarr; Parse tree &rarr; Symbol table &rarr; GOTO programs &rarr; GOTO program transformations &rarr; BMC &rarr; counterexample (goto_tracet) &rarr; printing ##

To be documented.

## Instrumentation: goto functions &rarr; goto functions ##

To be documented.

## Goto functions &rarr; BMC &rarr; Counterexample (trace) ##

To be documented.

## Trace &rarr; interpreter &rarr; memory map ##

To be documented.

## Goto functions &rarr; abstract interpretation ##

To be documented.

## Executables (flow of transformations): ##

### goto-cc ###

To be documented.

### goto-instrument ###

To be documented.

### cbmc ###

To be documented.

### goto-analyzer ###

To be documented.
