var index =
[
    [ "Installation Guide", "installation_guide.html", null ],
    [ "User Guide", "user_guide.html", null ],
    [ "Reference Guide", "reference_guide.html", null ],
    [ "Developer Guide", "developer_guide.html", null ],
    [ "CProver documentation", "cprover_documentation.html", [
      [ "Versions", "cprover_documentation.html#autotoc_md193", null ],
      [ "Report bugs", "cprover_documentation.html#autotoc_md194", null ],
      [ "Contributing to the code base", "cprover_documentation.html#autotoc_md195", null ],
      [ "License", "cprover_documentation.html#autotoc_md196", null ],
      [ "Overview of Documentation", "cprover_documentation.html#autotoc_md197", [
        [ "For users:", "cprover_documentation.html#autotoc_md198", null ],
        [ "For contributors:", "cprover_documentation.html#autotoc_md199", null ]
      ] ],
      [ "Memory Bounds Checking", "memory-bounds-checking.html", null ],
      [ "SATABS", "satabs.html", [
        [ "SATABS—Predicate Abstraction with SAT", "satabs.html#man_satabs", [
          [ "Automatic Program Verification with SATABS", "satabs.html#autotoc_md213", null ],
          [ "Installing SATABS", "satabs.html#man_install-satabs", [
            [ "Requirements", "satabs.html#autotoc_md214", null ],
            [ "Choosing and Installing a Model Checker", "satabs.html#autotoc_md215", null ],
            [ "Installing SATABS", "satabs.html#autotoc_md216", null ],
            [ "Requirements", "satabs.html#autotoc_md217", null ]
          ] ],
          [ "Overview", "satabs.html#man_satabs-overview", [
            [ "Working with Claims", "satabs.html#autotoc_md218", null ]
          ] ],
          [ "Programs that use Libraries", "satabs.html#man_satabs-libraries", null ],
          [ "Unit Testing with SATABS", "satabs.html#man_satabs-unit-test", [
            [ "Further Reading", "satabs.html#autotoc_md219", null ]
          ] ],
          [ "Background", "satabs.html#man_satabs-background", [
            [ "Sound Abstractions", "satabs.html#autotoc_md220", null ],
            [ "Spurious Counterexamples", "satabs.html#autotoc_md221", null ],
            [ "Automatic Refinement", "satabs.html#autotoc_md222", null ]
          ] ],
          [ "Tutorials", "satabs.html#man_satabs-tutorials", [
            [ "Reference Counting in Linux Device Drivers", "satabs.html#man_satabs-tutorial-driver", null ],
            [ "Buffer Overflow in a Mail Transfer Agent", "satabs.html#man_satabs-tutorial-aeon", null ]
          ] ]
        ] ]
      ] ],
      [ "Compilation and Development", "compilation-and-development.html", [
        [ "Compilation", "compilation-and-development.html#compilation-and-development-section-compilation", [
          [ "Makefiles", "compilation-and-development.html#compilation-and-development-subsection-makefiles", null ],
          [ "CMake files", "compilation-and-development.html#compilation-and-development-subsection-cmake-files", null ],
          [ "Personal configuration", "compilation-and-development.html#compilation-and-development-subsection-personal-configuration", [
            [ "config.inc", "compilation-and-development.html#compilation-and-development-subsubsection-config-inc", null ],
            [ "Macro DEBUG", "compilation-and-development.html#compilation-and-development-subsubsection-macro-debug", null ]
          ] ]
        ] ],
        [ "Running tests", "compilation-and-development.html#compilation-and-development-section-running-tests", [
          [ "Regression tests", "compilation-and-development.html#compilation-and-development-subsection-regression-tests", [
            [ "Running regression tests with make", "compilation-and-development.html#compilation-and-development-subsubsection-running-regression-tests-with-make", null ],
            [ "Running regression tests with CTest", "compilation-and-development.html#compilation-and-development-subsubsection-running-regression-tests-with-ctest", null ],
            [ "Running individual regression tests directly with test.pl", "compilation-and-development.html#compilation-and-development-subsubsection-running-individual-regression-tests-directly-with-test-pl", null ]
          ] ],
          [ "Unit tests", "compilation-and-development.html#compilation-and-development-subsection-unit-tests", null ],
          [ "Test coverage", "compilation-and-development.html#compilation-and-development-subsection-coverage", null ],
          [ "Using a different SAT solver", "compilation-and-development.html#compilation-and-development-subsection-sat-solver", null ]
        ] ],
        [ "Documentation", "compilation-and-development.html#compilation-and-development-section-documentation", null ],
        [ "Formatting", "compilation-and-development.html#compilation-and-development-section-formatting", null ],
        [ "Linting", "compilation-and-development.html#compilation-and-development-section-linting", null ],
        [ "Time profiling", "compilation-and-development.html#compilation-and-development-section-time-profiling", null ]
      ] ],
      [ "Background Concepts", "background-concepts.html", [
        [ "Representations", "background-concepts.html#representations_section", [
          [ "AST", "background-concepts.html#AST_section", [
            [ "Symbol tables and variable disambiguation", "background-concepts.html#symbol_table_section", null ]
          ] ],
          [ "Intermediate Representations (IR)", "background-concepts.html#IR_section", null ],
          [ "Control Flow Graphs (CFG)", "background-concepts.html#CFG_section", null ],
          [ "SSA", "background-concepts.html#SSA_section", null ],
          [ "Field Sensitivity", "background-concepts.html#field_sensitivity_section", null ]
        ] ],
        [ "Analysis techniques", "background-concepts.html#analysis_techniques_section", [
          [ "Bounded model checking", "background-concepts.html#BMC_section", [
            [ "Propositional logic and SAT solving", "background-concepts.html#propositional_logic_subsubsection", null ],
            [ "Using SAT to reason about data: Bit vectors", "background-concepts.html#bitvector_subsubsection", null ],
            [ "How bounded model checking works", "background-concepts.html#bmc_subsubsection", null ],
            [ "Where to go from here", "background-concepts.html#smt_etc_subsubsection", null ]
          ] ],
          [ "Static analysis", "background-concepts.html#static_analysis_section", [
            [ "Abstract Interpretation", "background-concepts.html#abstract_interpretation_section", null ]
          ] ]
        ] ],
        [ "Glossary", "background-concepts.html#Glossary_section", [
          [ "Instrument", "background-concepts.html#instrument_subsection", null ],
          [ "Flattening and Lowering", "background-concepts.html#flattening_lowering_subsection", null ],
          [ "Verification Condition", "background-concepts.html#verification_condition_subsection", null ]
        ] ]
      ] ],
      [ "CBMC Architecture", "cbmc-architecture.html", [
        [ "Concepts", "cbmc-architecture.html#autotoc_md170", [
          [ "Central data structures", "cbmc-architecture.html#autotoc_md171", null ],
          [ "{C, java bytecode} → Parse tree → Symbol table → GOTO programs → GOTO program transformations → BMC → counterexample (goto_tracet) → printing", "cbmc-architecture.html#autotoc_md172", null ],
          [ "Instrumentation: goto functions → goto functions", "cbmc-architecture.html#autotoc_md173", null ],
          [ "Goto functions → BMC → Counterexample (trace)", "cbmc-architecture.html#autotoc_md174", null ],
          [ "Trace → interpreter → memory map", "cbmc-architecture.html#autotoc_md175", null ],
          [ "Goto functions → abstract interpretation", "cbmc-architecture.html#autotoc_md176", null ],
          [ "Executables (flow of transformations):", "cbmc-architecture.html#autotoc_md177", [
            [ "goto-cc", "cbmc-architecture.html#autotoc_md178", null ],
            [ "goto-instrument", "cbmc-architecture.html#autotoc_md179", null ],
            [ "cbmc", "cbmc-architecture.html#autotoc_md180", null ],
            [ "goto-analyzer", "cbmc-architecture.html#autotoc_md181", null ]
          ] ]
        ] ],
        [ "Central Data Structures", "central-data-structures.html", [
          [ "Central Data Structures", "central-data-structures.html#autotoc_md182", [
            [ "GOTO models", "central-data-structures.html#autotoc_md183", null ],
            [ "goto_functiont", "central-data-structures.html#autotoc_md184", null ],
            [ "goto_programt", "central-data-structures.html#autotoc_md185", null ],
            [ "source_locationt", "central-data-structures.html#autotoc_md186", null ],
            [ "irept", "central-data-structures.html#autotoc_md187", null ]
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
      ] ],
      [ "Folder Walkthrough", "folder-walkthrough.html", null ],
      [ "Code Walkthrough", "code-walkthrough.html", [
        [ "Data structures: core structures and AST", "code-walkthrough.html#data-structures-core-structures-and-ast-section", null ],
        [ "Data structures: from AST to GOTO program", "code-walkthrough.html#data-structures-from-ast-to-goto-program-section", null ],
        [ "Front-end languages: generating codet from multiple languages", "code-walkthrough.html#front-end-languages-generating-codet-from-multiple-languages-section", [
          [ "language_filest, languaget classes:", "code-walkthrough.html#language-uit-section", null ],
          [ "C", "code-walkthrough.html#languages-c-section", null ],
          [ "C++", "code-walkthrough.html#languages-cpp-section", null ],
          [ "Java bytecode", "code-walkthrough.html#languages-java-section", null ]
        ] ],
        [ "Bmct class", "code-walkthrough.html#bmct-class-section", [
          [ "equation", "code-walkthrough.html#equation-section", null ]
        ] ],
        [ "Symbolic executors", "code-walkthrough.html#symbolic-executors-section", [
          [ "Symbolic execution", "code-walkthrough.html#symbolic-execution-section", null ]
        ] ],
        [ "Solvers infrastructure", "code-walkthrough.html#solvers-infrastructure-section", null ],
        [ "Static analysis APIs", "code-walkthrough.html#static-analysis-apis-section", null ]
      ] ],
      [ "Other Tools", "other-tools.html", [
        [ "Other Tools", "other-tools.html#autotoc_md207", null ]
      ] ],
      [ "Tutorials", "tutorial.html", [
        [ "CBMC Developer Tutorial", "tutorial.html#cbmc_tutorial", [
          [ "Initial setup", "tutorial.html#autotoc_md200", null ],
          [ "Whirlwind tour of the tools", "tutorial.html#autotoc_md201", [
            [ "Compiling with <tt>goto-cc</tt>", "tutorial.html#autotoc_md202", null ],
            [ "Viewing goto-programs", "tutorial.html#autotoc_md203", null ]
          ] ],
          [ "Learning about goto-programs", "tutorial.html#autotoc_md204", [
            [ "First steps with <tt>goto-instrument</tt>", "tutorial.html#autotoc_md205", null ],
            [ "Goto-program basics", "tutorial.html#autotoc_md206", null ]
          ] ]
        ] ]
      ] ]
    ] ],
    [ "Contributing documentation", "contributing_documentation.html", null ]
];