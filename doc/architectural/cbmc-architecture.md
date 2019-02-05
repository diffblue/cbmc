\ingroup module_hidden
\page cbmc-architecture CPROVER Architecture

\author Martin Brain, Peter Schrammel, Cesar Rodriguez

This chapter offers a high level description of the different modules that
make the CPROVER framework. At a glance, the framework comprises:

* An intermediate representation (IR) called GOTO program.
* Support to parse C, C++, and Java bytecode files into the GOTO IR.
* Support to perform bounded model checking of GOTO programs.
* Various static analyses, including interval analysis, alias analysis, FIXME

The CPROVER framework also provides various tools that aggregate multiple
modules together:

* CBMC and JBMC: bounded model checkers for C and Java
* `goto-analyzer`: a static analyzer and abstract interpreter of C and GOTO
  programs.
* `goto-cc`: a drop-in replacement for `gcc`, can be used to extract a GOTO program
  from a large project.
* `goto-instrument`: a tool for transformation of GOTO programs, including
  assertion instrumentation, slicing, loop unwinding, constant propagation, and
  other semantic transformations.
* `goto-diff`: FIXME
* Other tools, see \ref other-tools for more information.

CPROVER is structured in a similar fashion to a compiler. It has
language specific front-ends which perform limited syntactic analysis
and then convert to the GOTO intermediate format. The intermediate format can
be output to files (this is what `goto-cc` does) and are (informally)
referred to as “goto binaries” or “goto programs”. The back-end are
modules and tools that process this format, either directly from the front-end
or from it’s saved output.

The sections below provide a high-level overview of the various representations
(or core data structures) and transformations implemented in the CPROVER
framework.  In the sequel we asume that the reader is already familiar with how
to use CBMC. If that's not the case, please check the
[CPROVER User Manual](http://www.cprover.org/cprover-manual/), which describes
CBMC from a user perspective.

# Overview #

\htmlonly
<div class="image">
<img src="architecture.svg" width="950ex" alt="architecture.svg"/>
<!--
To modify the above picture:
1. Edit https://docs.google.com/drawings/d/1Kyh5afRKRZjfSYG_fnMWaN85928t59hYBTbnDXnbVEQ/edit
2. File > Download as > SVG
3. Update the file assets/architecture.svg
-->
</div>
\endhtmlonly

- high level explanation, common parts, different tools take different directions

# Overall Code Transformations #

The following diagram provides a detailed overview of the key classes that hold
relevant information as well as the transformations thata convert information
from one representation to the next one.

\htmlonly
<div class="image">
<img src="parsing-lowering.svg" width="2300ex" alt="architecture.svg"/>
<!--
To modify the above picture:
1. Edit https://docs.google.com/drawings/d/13S3MBPJJqepkNlzTp9gSmaIlg352JJ1nD3IcOfdNBSU/edit
2. File > Download as > SVG
3. Update the file assets/architecture.svg
-->
</div>
\endhtmlonly

FIXME
- Boxes corresponds to objects that represent information, usually code in
  various forms.
- Arrows represent transformations, and are usually labelled by the functions or
  methods that are overall responsible for that transformation. If you need to
  understand the code of CPROVER, those functions could be a good starting
  point.

## Parsing the Source ##

Input : the code
Output: a parse tree, classes X and Y

## Constructing the Symbol Table ##

Input: the parse tree
Output: the symbol table, the code is represented in codet

## Generating a GOTO program ##

Input: the parse tree
Output: the symbol table, the code is represented in codet

## GOTO program transformations ##

Describe here taht:
- different tools implement different transformations to prepare the program for
  various different things

## Bounded Model Checking ##

This this is only done by CBMC.

### Unfolding the Program into a an Equation ###

To be documented.

### Lowering the Equation into a SAT/SMT formula ###

To be documented.

### Getting a GOTO trace from a SAT model ###

To be documented.

## Static Analysis ##

To be documented.
Document here the main steps implemented in `goto-analyze`.

# Tools #

Different tools use different modules of the framework to implement their
functionality. The sections below briefly comment on

FIXME

how this happens.

## cbmc ##

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

Each node in the diagram above links to the
appropriate class or module documentation, describing that particular stage
in the CBMC pipeline.

### goto-analyzer ###

To be documented.

### goto-instrument ###

To be documented.

### goto-cc ###

To be documented.

