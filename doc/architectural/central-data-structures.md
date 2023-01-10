# Central Data Structures

The following is some light technical documentation of the major data structures
represented in the input transformation to Intermediate Representation (IR) inside
CBMC and the assorted CProver tools.

## goto_modelt

The `goto_modelt` is the main data structure that CBMC (and the other tools) use to
represent GOTO-IR (the `GOTO` Intermediate Representation).

A `goto_modelt` is effectively a product type, consisting of:

* A list of GOTO functions (pseudocode: `type goto_functionst = list<goto_functiont>`)
* A symbol table containing symbol references for the symbols contained in the
  GOTO functions (pseudocode: `type symbol_tablet = map<identifier, symbolt>`).

The abstract interface of `goto_modelt` is outlined in the file
[`src/goto-programs/abstract_goto_model.h`](../../src/goto-programs/abstract_goto_model.h).

## goto_functiont

A `goto_functiont` is also a product type. It's designed to represent a function
at the IR level, and effectively it's the following ADT (in pseudocode):

```js
type goto_functiont {
    goto_programt body
    list<identifiers> parameters
}
```

Of the two types listed above, the `parameters` one should be self-documenting,
(the values of these are later looked up in the symbol table), so we're going to
focus next on the type `goto_programt`

## goto_programt

A `goto_programt` is a container of GOTO-IR instructions. In pseudocode, it would
look like `type goto_programt = list<goto_instructiont>`.

An instruction (`goto_instructiont`) is another product type, describing a GOTO level
instruction with the following 3 component subtypes, again in pseudocode:

```js
type goto_instructiont {
    instruction_type instr_type
    instruction      statement
    guard            boolean_expr
}
```

The above subtypes are just illustrative, so we will provide some extra explanation for
these:

* The `instruction_type` above corresponds to the `goto_program_instruction_typet` type
  listed in [`goto_program.h`](../../src/goto-programs/goto_program.h)
  * For illustration purposes, some instruction types are `assign`, `function_call`, `return`,
    etc.
* The `instruction` is a statement represented by a `goto_instruction_codet`.
  * A `goto_instruction_codet` is a `codet` (a data structure broadly representing a statement
    inside CBMC) that contains the actual GOTO-IR instruction.
  * You can distinguish different statements by inspecting the `irep` element `ID_statement`.
* The `guard` is an `exprt` (A CBMC data structure broadly representing an expression)
  that is expected to have type `bool`.
  * This is optional - not every instruction is expected to have a `guard` associated with it.

## source_locationt

Another important data structure that needs to be discussed at this point is
`source_locationt`.

This is an `irept`. `irep`s are the central data structure that model most entities inside
CBMC and the assorted tools - effectively a node/map like data structure that forms a hierachical
tree that ends up modeling graphs like ASTs, CFGs, etc. (This will be further discussed in
a dedicated page).

`source_locationt` are attached into various `exprt`s (the data structure representing
various expressions, usually the result of some early processing, e.g. the result of the
frontend parsing a file).

This means that `codet`s, representing GOTO-IR instructions *also* have a `source_locationt`
attached to them, by virtue of inheriting from `exprt`.

For the most part, `source_locationt` is something that is only being used when we print
various nodes (for property listing, counterexample/trace printing, etc).

It might be possible that a specific source location might point to a CBMC instrumentation
primitive (which might be reported as a `built-in-addition`) or there might even be no-source
location (because it might be part of harnesses generated as an example, that have no presence
in the user code).
