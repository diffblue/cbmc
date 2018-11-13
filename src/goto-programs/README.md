\ingroup module_hidden
\defgroup goto-programs goto-programs

# Folder goto-programs

\author Kareem Khazem, Martin Brain

\section goto-programs-overview Overview
Goto programs are the intermediate representation of the CPROVER tool
chain. They are language independent and similar to many of the compiler
intermediate languages. Each function is a
list of instructions, each of which has a type (one of 19 kinds of
instruction), a code expression, a guard expression and potentially some
targets for the next instruction. They are not natively in static
single-assign (SSA) form. Transitions are nondeterministic (although in
practise the guards on the transitions normally cover form a disjoint
cover of all possibilities). Local variables have non-deterministic
values if they are not initialised. Goto programs can be serialised
in a binary (wrapped in ELF headers) format or in XML (see the various
`_serialization` files).

The `cbmc` option `--show-goto-programs` is often a good starting point
as it outputs goto-programs in a human readable form. However there are
a few things to be aware of. Functions have an internal name (for
example `c::f00`) and a ‘pretty name’ (for example `f00`) and which is
used depends on whether it is internal or being presented to the user.
`NONDET(some_type)` is use to represent a nondeterministic value.
`IF guard GOTO x` represents a GOTO instruction with a guard, not a distinct
`IF` instruction.
The comment lines are generated from the `source_location` field
of the `instructiont` structure.

GOTO programs are commonly produced using the `initialize_goto_model` function,
which combines the complete process from command-line arguments specifying
source code files, through parsing and generating a symbol table, to finally
producing GOTO functions.

Alternatively `lazy_goto_modelt` can be used, which facilitates producing GOTO
functions on demand. See \ref section-lazy-conversion for more details on this
method.

\section goto_data_structures Data Structures

A \ref goto_functionst object contains a set of GOTO programs. Note the
counter-intuitive naming: `goto_functionst` instances are the top level
structure representing the program and contain `goto_programt` instances
which represent the individual functions.

An instance of \ref goto_programt is effectively a list of
instructions (a nested class called \ref goto_programt::instructiont).
It is important
to use the copy and insertion functions that are provided as iterators
are used to link instructions to their predecessors and targets and
careless manipulation of the list could break these.

Individual instructions are instances of type \ref goto_programt::instructiont.
They represent one step in the function.  Each has a type, an instance of
\ref goto_program_instruction_typet which denotes what kind of instruction
it is. They can be computational (such as `ASSIGN` or `FUNCTION_CALL`),
logical (such as `ASSUME` and `ASSERT`) or informational (such as
`LOCATION` and `DEAD`). At the time of writing there are 19 possible
values for `goto_program_instruction_typet` / kinds of instruction.
Instructions also have a guard field (the condition under which it is
executed) and a code field (what the instruction does). These may be
empty depending on the kind of instruction.
These are of type \ref exprt and \ref codet respectively.
The next instructions (remembering that transitions may be
non-deterministic) are given by the list `targets` (with the
corresponding list of labels `labels`) and the corresponding set of
previous instructions is get by `incoming_edges`. Finally `instructiont`
has informational `function` and `source_location` fields that indicate where
they are in the source code.

\section goto-conversion Goto Conversion

In the \ref goto-programs directory.

**Key classes:**
* goto_programt
* goto_functionst
* \ref goto_programt::instructiont

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

At this stage, CBMC constructs a goto-program from a symbol table.
Each symbol in the symbol table with function type (that is, the symbol's `type`
field contains a \ref code_typet) will be converted to a corresponding GOTO
program. The parse tree and source file are not used at all for this step.

The conversion happens in two phases:

1. Function `goto_convertt::convert` turns each `codet` in the symbol table
   into corresponding GOTO instructions.
2. `goto_convertt::finish_gotos` and others populate the `GOTO` and `CATCH`
   instructions' `targets` members, pointing to their possible successors.
   `DEAD` instructions are also added when GOTO instructions branch out of one
   or more lexical blocks.

Here is an example of a simple C program being converted into GOTO code (note
the `targets` member of each instruction isn't populated yet):

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

The `codet` representation of method bodies that is stored in the symbol table
resembles C code quite strongly: it uses lexical variable scoping and has
complex control-flow constructs such as `code_whilet` and `code_ifthenelset`.
In converting to a GOTO program this structure is changed in several ways:

* Variable lifespan implied by \ref code_declt instructions and lexical scopes
  described by \ref code_blockt nodes is replaced by `DECL` and corresponding
  `DEAD` instructions. There are therefore no lexical scopes in GOTO programs
  (not even local variable death on function exit is enforced).

* Expressions with side-effects are explicitly ordered so that there is one
  effect per instruction (apart from function call instructions, which can
  still have many). For example, `y = f() + x++` will have become something like
  `tmp1 = f(); y = tmp1 + x; x = x + 1;`

* Compound blocks are eliminated. There are several subclasses of
  \ref codet that count as 'compound blocks;' therefore, later stages in
  the CBMC pipeline that switch over the codet subtype of a particular
  instruction should not need to consider these types. In particular:

  * code_ifthenelset is turned into GOTOs. In particular, the bodies of
    the conditionals are flattened into lists of instructions, inline
    with the rest of the instruction in the goto_programt. The guard of
    the conditional is placed onto the
    \ref goto_programt::instructiont::guard "guard" member of
    an instruction whose code member is of type \ref code_gotot. The
    \ref goto_programt::instructiont::targets "targets" member
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
  instruction.

\section section-goto-transforms Subsequent Transformation

It is normal for a program that calls `goto_convert` to immediately pass the
GOTO functions through one or more transformations. For example, the ubiquitous
`remove_returns` transformation turns the method return sequence generated by
`goto_convert` (something like `RETURN x; GOTO end;`) into
`function_name#return_value = x; GOTO end;`, and a callsite
`y = function_name();` into `function_name(); y = function_name#return_value;`.

Some subsequent parts of the CBMC pipeline assume that one or more of these
transforms has been applied, making them effectively mandatory in that case.

Common transformations include:

* Removing superfluous SKIP instructions (`remove_skip`)
* Converting indirect function calls into dispatch tables over direct calls
  (`remove_virtual_functions` and `remove_function_pointers`)
* Adding checks for null-pointer dereferences, arithmetic overflow and other
  undefined behaviour (`goto_check`)
* Adding code coverage assertions (`instrument_cover_goals`).

By convention these post-convert transformations are applied by a driver program
in a function named `process_goto_program` or `process_goto_functions`; examples
of these can be found in `cbmc_parse_optionst`, `goto_analyzer_parse_optionst`
and `goto_instrument_parse_optionst` among others.

\section section-lazy-conversion Lazy GOTO Conversion

The conventional source-code-to-GOTO-program pipeline is horizontally
structured: all source-file information is converted into a symbol table, then
each symbol-table method is converted into a GOTO program, then each transform
is run over the whole GOTO-model in turn. This is fine when the GOTO model
consumer will use most or all of the results of conversion, but if not then
lazy conversion may be beneficial.

Lazy conversion is coordinated by `lazy_goto_modelt`. Early source code parsing
proceeds as usual, but while the same symbol table symbols are created as using
`initialize_goto_model`, method bodies in the symbol table are not populated.
`lazy_goto_modelt::get_goto_function` then allows each function to be converted
on demand, passing individually through symbol-table `codet` production, GOTO
conversion and driver-program transformation.

`goto_symext` is able to use such a lazy GOTO model in place of the usual
`goto_modelt`, enabling it to create GOTO programs on demand, and thus avoid
spending time and memory generating GOTO programs that symex determines cannot
in fact be reached. This is particularly useful when the source program contains
many indirect calls (virtual function calls, or calls via function pointer), as
the `remove_virtual_functions` and `remove_function_pointers` passes treat these
very conservatively, producing large dispatch tables of possible callees which
symex often finds to be largely unreachable.

JBMC exhibits typical usage of `lazy_goto_modelt` when it is called with
`--symex-driven-lazy-loading`. It defines a function
`jbmc_parse_optionst::process_goto_function` which performs driver-program-
specific post-GOTO-convert transformation. The lazy GOTO model is then passed to
`goto_symext`, which will trigger symbol-table population, GOTO conversion
and post-processing as needed.

\section section-goto-binary Binary Representation

An instance of `::goto_modelt` can be serialised to a binary stream (which is
typically a file on the disk), and later deserialised from that stream back to
an equivalent `::goto_modelt` instance.

\subsection subsection-goto-binary-serialisation Serialisation

The serialisation is implemented in C++ modules:
  - `write_goto_binary.h`
  - `write_goto_binary.cpp`

To serialise a `::goto_modelt` instance `gm` to a stream `ostr` call the
function `::write_goto_binary`, e.g. `write_goto_binary(ostr, gm)`.

The content of the written stream will have this structure:
  - The header:
    - A magic number: byte `0x7f` followed by 3 characters `GBF`.
    - A version number written in the 7-bit encoding (see [number serialisation](\ref irep-serialization-numbers)). Currently, only version `4` is supported.
  - The symbol table:
    - The number of symbols in the table in the 7-bit encoding.
    - The array of individual symbols in the table. Each written symbol `s` has this structure:
      - The `::irept` instance `s.type`.
      - The `::irept` instance `s.value`.
      - The `::irept` instance `s.location`.
      - The string `s.name`.
      - The string `s.module`.
      - The string `s.base_name`.
      - The string `s.mode`.
      - The string `s.pretty_name`.
      - The number `0` in the 7-bit encoding.
      - The flags word in the 7-bit encoding. The bits in the flags word correspond to the following `Boolean` fields (from the most significant bit):
        - `s.is_weak`
        - `s.is_type`
        - `s.is_property`
        - `s.is_macro`
        - `s.is_exported`
        - `s.is_input`
        - `s.is_output`
        - `s.is_state_var`
        - `s.is_parameter`
        - `s.is_auxiliary`
        - `0` (corresponding to `s.binding`, i.e. we always clear this info)
        - `s.is_lvalue`
        - `s.is_static_lifetime`
        - `s.is_thread_local`
        - `s.is_file_local`
        - `s.is_extern`
        - `s.is_volatile`
  - The functions with bodies, i.e. those missing a body are skipped.
    - The number of functions with bodies in the 7-bit encoding.
    - The array of individual functions with bodies. Each written function has this structure:
      - The string with the name of the function.
      - The number of instructions in the body of the function in the 7-bit encoding.
      - The array of individual instructions in function's body. Each written instruction `I` has this structure:
        - The `::irept` instance `I.code`, i.e. data of the instruction, like arguments.
        - The string `I.function`, i.e. the name of the function this instruction belongs to.
        - The `::irept` instance `I.source_location`, i.e. the reference to the original source code (file, line).
        - The word in the 7-bit encoding `I.type`, i.e. the op-code of the instruction.
        - The `::irept` instance `I.guard`.
        - The empty string (representing former `I.event`).
        - The word in the 7-bit encoding `I.target_number`, i.e. the jump target to this instruction from other instructions.
        - The word in the 7-bit encoding `I.targets.size()`, i.e. the count of jump targets from this instruction.
        - The array of individual jump targets from this instruction, each written as a word in the 7-bit encoding.
        - The word in the 7-bit encoding `I.labels.size()`.
        - The array of individual labels, each written as a word in the 7-bit encoding.

An important propery of the serialisation is that each serialised `::irept`
instance occurs in the stream exactly once. Namely, in the position of
its first serialisation query. All other such queries save only a hash
code (i.e. reference) of the `::irept` instance.

A similar strategy is used for serialisation of string constants
shared amongst `::irept` instances. Such a string is fully saved only in
the first serialisation query of an `::irept` instance it appears in and
all other queries only save its integer hash code.

Details about serialisation of `::irept` instances, strings, and words in
7-bit encoding can be found [here](\ref irep-serialization).

\subsection subsection-goto-binary-deserialisation Deserialisation

The deserialisation is implemented in C++ modules:
  - `read_goto_binary.h`
  - `read_goto_binary.cpp`
  - `read_bin_goto_object.h`
  - `read_bin_goto_object.cpp`

The first two modules are responsible for location of the stream with the
serialised data within a passed file. And the remaining two modules
perform the actual deserialisation of a `::goto_modelt` instance from
the located stream.

To deserialise a `::goto_modelt` instance `gm` from a file
`/some/path/name.gbf` call the function `::read_goto_binary`, e.g.
`read_goto_binary("/some/path/name.gbf", gm, message_handler)`, where
`message_handler` must be an instance of `::message_handlert` and serves
for reporting issues during the process.

The passed binary file is assumed to have the same structure as described in
the [previous subsection](\ref subsection-goto-binary-serialisation).
The process of the deserialisation does not involve any seeking in the file.
The content is read linearly from the beginning to the end. `::irept` instances
and their string constants are deserialised into the memory only once at their
first occurrences in the stream. All subsequent deserialisation queries are
resolved as in-memory references to already deserialised the `::irept`
instances and/or strings, based on hash code matching.

NOTE: The first deserialisation is detected so that the loaded hash code
is new. That implies that the full definition follows right after the hash.

Details about serialisation of `::irept` instances, strings, and words in
7-bit encoding can be found [here](\ref irep-serialization).

\subsubsection subsection-goto-binary-deserialisation-from-elf Deserialisation from ELF image

One can decide to store the serialised stream as a separate section, named
`goto-cc`, into an ELF image. Then the deserialisation has a support of
automatic detection of that section in an ELF file and the deserialisation
will be automatically started from that section.

For reading the ELF images there is used an instance of `::elf_readert`
implemented in the C++ module:
  - `elf_reader.h`
  - `elf_reader.cpp`

\subsubsection subsection-goto-binary-deserialisation-from-mach-o-fat-image Deserialisation from Mach-O fat image

One can decide to store the serialised stream into Mach-O fat image as a
separate non-empty section with flags `CPU_TYPE_HPPA` and
`CPU_SUBTYPE_HPPA_7100LC`. Then the deserialisation has a support of
automatic detection of that section in a Mach-O fat image, extraction
of the section from the emage into a temporary file (this is done by
calling `lipo` utility with `-thin hppa7100LC` option), and the
deserialisation will be automatically started from that temporary
file.

For reading the Mach-O fat images there is used an instance of
`::osx_fat_readert` implemented in the C++ module:
  - `osx_fat_reader.h`
  - `osx_fat_reader.cpp`

NOTE: This functionality is available only when the modules are built
on a MacOS machine.

\subsubsection subsection-goto-binary-is-binary-file Checking file type

You can use function `::is_goto_binary` to check whether a passed file contains
a deserialised `::goto_modelt` instance or not. This is done by checking the
magic number of the stream (see subsection
[Serialisation](\ref subsection-goto-binary-serialisation)). However, in the
case when the deserialised data were stored into ELF or Mach-O fat image, then
only the check for presence of the concrete section in the image is performed.

\subsubsection subsection-goto-binary-deserialisation-linking Linking Goto Models

Similar to linking of object files together by C/C++ linker, the module
provides linking of a dereserialised `::goto_modelt` instance into a given
(i.e. previously deserialised or otherwise created) `::goto_modelt` instance.

This is implemented in function `::read_object_and_link`. The function first
deserialises the passed file into a temporary `::goto_modelt` instance, and
then it performs 'linking' of the temporary into a passed destination
`::goto_modelt` instance.

Details about linking of `::goto_modelt` instances can be found
[here](\ref section-linking-goto-models).


\section section-linking-goto-models Linking Goto Models

C++ modules:
  - `link_goto_model.h`
  - `link_goto_model.cpp`

Dependencies:
  - [linking folder](\ref linking).
  - [typecheck](\ref section-goto-typecheck).
