var cbmc_architecture =
[
    [ "Concepts", "cbmc-architecture.html#autotoc_md168", [
      [ "Central data structures", "cbmc-architecture.html#autotoc_md169", null ],
      [ "{C, java bytecode} → Parse tree → Symbol table → GOTO programs → GOTO program transformations → BMC → counterexample (goto_tracet) → printing", "cbmc-architecture.html#autotoc_md170", null ],
      [ "Instrumentation: goto functions → goto functions", "cbmc-architecture.html#autotoc_md171", null ],
      [ "Goto functions → BMC → Counterexample (trace)", "cbmc-architecture.html#autotoc_md172", null ],
      [ "Trace → interpreter → memory map", "cbmc-architecture.html#autotoc_md173", null ],
      [ "Goto functions → abstract interpretation", "cbmc-architecture.html#autotoc_md174", null ],
      [ "Executables (flow of transformations):", "cbmc-architecture.html#autotoc_md175", [
        [ "goto-cc", "cbmc-architecture.html#autotoc_md176", null ],
        [ "goto-instrument", "cbmc-architecture.html#autotoc_md177", null ],
        [ "cbmc", "cbmc-architecture.html#autotoc_md178", null ],
        [ "goto-analyzer", "cbmc-architecture.html#autotoc_md179", null ]
      ] ]
    ] ],
    [ "Central Data Structures", "central-data-structures.html", [
      [ "Central Data Structures", "central-data-structures.html#autotoc_md180", [
        [ "GOTO models", "central-data-structures.html#autotoc_md181", null ],
        [ "goto_functiont", "central-data-structures.html#autotoc_md182", null ],
        [ "goto_programt", "central-data-structures.html#autotoc_md183", null ],
        [ "source_locationt", "central-data-structures.html#autotoc_md184", null ],
        [ "irept", "central-data-structures.html#autotoc_md185", null ]
      ] ]
    ] ],
    [ "Goto Program Transformations", "goto-program-transformations.html", [
      [ "Core Transformation Passes", "goto-program-transformations.html#required-transforms", [
        [ "Removal/Lowering of Assembly", "goto-program-transformations.html#assembly-transform", null ],
        [ "Linking of Standard Libraries", "goto-program-transformations.html#linking-transform", null ],
        [ "Removal/Lowering of Function Pointers", "goto-program-transformations.html#function-pointer-transform", null ],
        [ "Memory Mapped IO Instrumentation", "goto-program-transformations.html#mmio-transform", null ],
        [ "Instrument/Remove Preconditions", "goto-program-transformations.html#precondition-transform", null ],
        [ "Removal/Lowering of Return Statements", "goto-program-transformations.html#returns-transform", null ],
        [ "Remove/Lower Vector Typed Expressions", "goto-program-transformations.html#vector-transform", null ],
        [ "Remove/Lower Complex Typed Expressions", "goto-program-transformations.html#complex-transform", null ],
        [ "Rewrite Unions", "goto-program-transformations.html#unions-transform", null ],
        [ "goto_check_c", "goto-program-transformations.html#check-c-transform", null ],
        [ "Adjust Float Expressions", "goto-program-transformations.html#floats-transform", null ],
        [ "Goto Functions Update", "goto-program-transformations.html#update-transform", null ],
        [ "Add Failed Symbols", "goto-program-transformations.html#failed-symbols-transform", null ],
        [ "Remove Skip Instructions", "goto-program-transformations.html#remove-skip-transform", null ],
        [ "Label Properties", "goto-program-transformations.html#properties-transform", null ]
      ] ],
      [ "Optional Transformation Passes", "goto-program-transformations.html#optional-transforms", [
        [ "String Instrumentation", "goto-program-transformations.html#string-instrument-transform", null ],
        [ "Partial Inlining", "goto-program-transformations.html#inlining-transform", null ],
        [ "Transform Assertions Assumptions", "goto-program-transformations.html#assertions-transform", null ],
        [ "String Abstraction", "goto-program-transformations.html#string-abstraction-transform", null ],
        [ "Add Non-Deterministic Initialisation of Global Scoped Variables", "goto-program-transformations.html#nondet-transform", null ],
        [ "Remove Unused Functions", "goto-program-transformations.html#unused-functions-transform", null ],
        [ "Add Coverage Goals", "goto-program-transformations.html#coverage-transform", null ],
        [ "Slicing", "goto-program-transformations.html#slicing-transforms", null ]
      ] ]
    ] ]
];