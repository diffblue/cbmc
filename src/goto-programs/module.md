\ingroup module_hidden
\defgroup module_goto-programs Goto Conversion & Instrumentation

\author Kareem Khazem

\section goto-conversion Goto Conversion

In the \ref goto-programs directory.

**Key classes:**
* goto_programt
* goto_functionst
* \ref goto_program_templatet::instructiont

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="goto conversion"];
  3 [shape=none, label=""];
  1 -> 2 [label="Symbol table"];
  2 -> 3 [label="goto-programs, goto-functions, symbol table"];
}
\enddot

At this stage, CBMC constructs a goto-program from a symbol table. It
does not use the parse tree or the source file at all for this step. This
may seem surprising, because the symbols are stored in a hash table and
therefore have no intrinsic order; nevertheless, every \ref symbolt is
associated with a \ref source_locationt, allowing CBMC to figure out the
lexical order.

The structure of what is informally called a goto-program follows.  The
entire target program is converted to a single \ref goto_functionst
object. The goto functions contains a set of \ref goto_programt objects;
each of these correspond to a "function" or "method" in the target
program. Each goto_program contains a list of
\ref goto_program_templatet::instructiont "instructions"; each
instruction contains an associated statement---these are subtypes of
\ref codet. Each instruction also contains a "target", which will be
empty for now.

\dot
digraph G{
  graph [nojustify=true];
  node [shape=box];
  compound=true;

  subgraph cluster_src {
    1 [shape="none", label="source files"];
    2 [label="file1.c\n-----------\nint main(){
  int x = 5;
  if(x > 7){
    x = 9; } }

void foo(){}"];
  1 -> 2 [color=white];

    100 [label="file2.c\n--------\nchar bar(){ }"];
    2 -> 100 [color=white];
  }

  1 -> 3 [label="corresponds to", lhead=cluster_goto,
  ltail=cluster_src];

  subgraph cluster_goto {
    3 [label="a\ngoto_functionst", URL="\ref goto_functionst", shape=none];
    4 [label="function_map\n(a map from irep_idt\nto goto_programt)"];
  }
  4 -> 5 [lhead=cluster_funmap, label="value:"];

  subgraph cluster_funmap {
    9 [label="bar\n(an irep_idt)", URL="\ref irep_idt"];
   10 [label="a goto_programt", URL="\ref goto_programt"];
    9->10 [label="maps to"];

    5 [label="main\n(an irep_idt)", URL="\ref irep_idt"];

    7 [label="foo\n(an irep_idt)", URL="\ref irep_idt"];
    8 [label="a goto_programt", URL="\ref goto_programt"];
    7->8 [label="maps to"];

    subgraph cluster_goto_program {
     11 [shape=none, label="a\ngoto_programt", URL="\ref goto_programt"];
     12 [label="instructions\n(a list of instructiont)"];
    }
    5 -> 11 [lhead=cluster_goto_program, label="maps to:"];

  }

  12 -> target1 [lhead=cluster_instructions];

  subgraph cluster_instructions {
    subgraph cluster_ins1{
      code1 [label="code", URL="\ref codet"];
      target1 [label="target"];
    }

    target1 -> target2 [color=white,lhead=cluster_ins2,
    ltail=cluster_ins1];

    subgraph cluster_ins2{
      code2 [label="code", URL="\ref codet"];
      target2 [label="target"];
    }

    target2 -> target3 [color=white,lhead=cluster_ins3,
    ltail=cluster_ins2];

    subgraph cluster_ins3{
      code3 [label="code", URL="\ref codet"];
      target3 [label="target"];
    }

    target3 -> target4 [color=white,lhead=cluster_ins4,
    ltail=cluster_ins3];

    subgraph cluster_ins4{
      code4 [label="code", URL="\ref codet"];
      target4 [label="target"];
    }

  }

  subgraph cluster_decl {
    decl1 [label="type:\ncode_declt", URL="\ref code_declt",
           shape=none];
    subgraph cluster_decl_in{
      cluster_decl_in_1 [label="symbol()", shape=none];
      cluster_decl_in_2 [label="x"];
      cluster_decl_in_1 -> cluster_decl_in_2 [color=white];
    }
    decl1 -> cluster_decl_in_1 [lhead="cluster_decl_in", color=white];
  }
  code1 -> decl1 [lhead=cluster_decl];

  subgraph cluster_assign1 {
    assign1 [label="type:\ncode_assignt", URL="\ref code_assignt",
           shape=none];
    subgraph cluster_assign1_in{
      cluster_assign1_in_1 [label="lhs()", shape=none];
      cluster_assign1_in_2 [label="x"];
      cluster_assign1_in_1 -> cluster_assign1_in_2 [color=white];

      cluster_assign1_in_3 [label="rhs()", shape=none];
      cluster_assign1_in_4 [label="5"];
      cluster_assign1_in_3 -> cluster_assign1_in_4 [color=white];
    }
    assign1 -> cluster_assign1_in_1 [lhead="cluster_assign1_in", color=white];
  }
  code2 -> assign1 [lhead=cluster_assign1];

  subgraph cluster_if {
    if [label="type:\ncode_ifthenelset", URL="\ref code_ifthenelset",
           shape=none];
    if_body [label="..."];
    if -> if_body [color=white];
  }
  code3 -> if [lhead=cluster_if];

  subgraph cluster_assign2 {
    assign2 [label="type:\ncode_assignt", URL="\ref code_assignt",
           shape=none];
    subgraph cluster_assign2_in{
      cluster_assign2_in_1 [label="lhs()", shape=none];
      cluster_assign2_in_2 [label="x"];
      cluster_assign2_in_1 -> cluster_assign2_in_2 [color=white];

      cluster_assign2_in_3 [label="rhs()", shape=none];
      cluster_assign2_in_4 [label="9"];
      cluster_assign2_in_3 -> cluster_assign2_in_4 [color=white];
    }
    assign2 -> cluster_assign2_in_1 [lhead="cluster_assign2_in", color=white];
  }
  code4 -> assign2 [lhead=cluster_assign2];

}
\enddot

This is not the final form of the goto-functions, since the lists of
instructions will be 'normalized' in the next step (Instrumentation),
which removes some instructions and adds targets to others.

Note that goto_programt and goto_functionst are each template
instantiations; they are currently the *only* specialization of
goto_program_templatet and goto_functions_templatet, respectively. This
means that the generated Doxygen documentation can be somewhat obtuse
about the actual types of things, and is unable to generate links to the
correct classes. Note that the
\ref goto_program_templatet::instructiont::code "code" member of a
goto_programt's instruction has type \ref codet (its type in the
goto_program_templatet documentation is given as "codeT", as this is the
name of the template's type parameter); similarly, the type of a guard
of an instruction is \ref guardt.

---
\section instrumentation Instrumentation

In the \ref goto-programs directory.

**Key classes:**
* goto_programt
* goto_functionst
* \ref goto_program_templatet::instructiont

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="goto conversion"];
  3 [shape=none, label=""];
  1 -> 2 [label="goto-programs, goto-functions, symbol table"];
  2 -> 3 [label="transformed goto-programs"];
}
\enddot

This stage applies several transformations to the goto-programs from the
previous stage:

* The diagram in the previous stage showed a goto_programt with four
  instructions, but real programs usually yield instruction lists that
  are littered with \ref code_skipt "skip" statements. The
  instrumentation stage removes the majority of these.

* Function pointers are removed. They are turned into switch statements
  (but see the next point; switch statements are further transformed).

* Compound blocks are eliminated. There are several subclasses of
  \ref codet that count as 'compound blocks;' therefore, later stages in
  the CBMC pipeline that switch over the codet subtype of a particular
  instruction should not need to consider these types. In particular:

  * code_ifthenelset is turned into GOTOs. In particular, the bodies of
    the conditionals are flattened into lists of instructions, inline
    with the rest of the instruction in the goto_programt. The guard of
    the conditional is placed onto the
    \ref goto_program_templatet::instructiont::guard "guard" member of
    an instruction whose code member is of type \ref code_gotot. The
    \ref goto_program_templatet::instructiont::targets "targets" member
    of that instruction points to the appropriate branch of the
    conditional. (Note that although instructions have a list of
    targets, in practice an instruction should only ever have at most
    one target; you should check this invariant with an assertion if you
    rely on it).

    The order of instructions in a list of instructions---as well as the
    targets of GOTOs---are both displayed as arrows when viewing a
    goto-program as a Graphviz DOT file with `goto-instrument --dot`.
    The semantics of a goto-program is: the next instruction is the next
    instruction in the list, unless the current instruction has a
    target; in that case, check the guard of the instruction, and jump
    to the target if the guard evaluates to true.

  * switch statements, for and while loops, and try-catches are also
    transformed into lists of instructions guarded by GOTOs.

  * \ref code_blockt "code blocks" are transformed into lists of
    instructions.

* \ref code_returnt "return statements" are transformed into
  (unconditional) GOTOs whose target is the \ref END_FUNCTION
  instruction. Each goto_programt should have precisely one such
  instruction. Note the presence of \ref code_deadt, which has a
  \ref code_deadt::symbol() "symbol()" member. Deads mark symbols that
  have just gone out of scope; typically, a GOTO that jumps to an
  END_FUNCTION instruction is preceded by a series of deads. Deads also
  follow sequences of instructions that were part of the body of a
  block (loop, conditional etc.) if there were symbols declared in that
  block.

This stage concludes the *analysis-independent* program transformations.
