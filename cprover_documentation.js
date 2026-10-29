var cprover_documentation =
[
    [ "Versions", "cprover_documentation.html#autotoc_md193", null ],
    [ "Report bugs", "cprover_documentation.html#autotoc_md194", null ],
    [ "Contributing to the code base", "cprover_documentation.html#autotoc_md195", null ],
    [ "License", "cprover_documentation.html#autotoc_md196", null ],
    [ "Overview of Documentation", "cprover_documentation.html#autotoc_md197", [
      [ "For users:", "cprover_documentation.html#autotoc_md198", null ],
      [ "For contributors:", "cprover_documentation.html#autotoc_md199", null ]
    ] ],
    [ "SATABS", "satabs.html", [
      [ "SATABS&mdash;Predicate Abstraction with SAT", "satabs.html#man_satabs", [
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
      ] ],
      [ "Compilation", "group__module__hidden.html#compilation-and-development-section-compilation", [
        [ "Makefiles", "group__module__hidden.html#compilation-and-development-subsection-makefiles", null ],
        [ "CMake files", "group__module__hidden.html#compilation-and-development-subsection-cmake-files", null ],
        [ "Personal configuration", "group__module__hidden.html#compilation-and-development-subsection-personal-configuration", [
          [ "config.inc", "group__module__hidden.html#compilation-and-development-subsubsection-config-inc", null ],
          [ "Macro DEBUG", "group__module__hidden.html#compilation-and-development-subsubsection-macro-debug", null ]
        ] ]
      ] ],
      [ "Running tests", "group__module__hidden.html#compilation-and-development-section-running-tests", [
        [ "Regression tests", "group__module__hidden.html#compilation-and-development-subsection-regression-tests", [
          [ "Running regression tests with make", "group__module__hidden.html#compilation-and-development-subsubsection-running-regression-tests-with-make", null ],
          [ "Running regression tests with CTest", "group__module__hidden.html#compilation-and-development-subsubsection-running-regression-tests-with-ctest", null ],
          [ "Running individual regression tests directly with test.pl", "group__module__hidden.html#compilation-and-development-subsubsection-running-individual-regression-tests-directly-with-test-pl", null ]
        ] ],
        [ "Unit tests", "group__module__hidden.html#compilation-and-development-subsection-unit-tests", null ],
        [ "Test coverage", "group__module__hidden.html#compilation-and-development-subsection-coverage", null ],
        [ "Using a different SAT solver", "group__module__hidden.html#compilation-and-development-subsection-sat-solver", null ]
      ] ],
      [ "Documentation", "group__module__hidden.html#compilation-and-development-section-documentation", null ],
      [ "Formatting", "group__module__hidden.html#compilation-and-development-section-formatting", null ],
      [ "Linting", "group__module__hidden.html#compilation-and-development-section-linting", null ],
      [ "Time profiling", "group__module__hidden.html#compilation-and-development-section-time-profiling", [
        [ "Profiling with perf (recommended)", "group__module__hidden.html#compilation-and-development-subsection-perf-profiling", null ],
        [ "Profiling with gprof", "group__module__hidden.html#compilation-and-development-subsection-gprof-profiling", null ]
      ] ],
      [ "Representations", "group__module__hidden.html#representations_section", [
        [ "AST", "group__module__hidden.html#AST_section", [
          [ "Symbol tables and variable disambiguation", "group__module__hidden.html#symbol_table_section", null ]
        ] ],
        [ "Intermediate Representations (IR)", "group__module__hidden.html#IR_section", null ],
        [ "Control Flow Graphs (CFG)", "group__module__hidden.html#CFG_section", null ],
        [ "SSA", "group__module__hidden.html#SSA_section", null ],
        [ "Field Sensitivity", "group__module__hidden.html#field_sensitivity_section", null ]
      ] ],
      [ "Analysis techniques", "group__module__hidden.html#analysis_techniques_section", [
        [ "Bounded model checking", "group__module__hidden.html#BMC_section", [
          [ "Propositional logic and SAT solving", "group__module__hidden.html#propositional_logic_subsubsection", null ],
          [ "Using SAT to reason about data: Bit vectors", "group__module__hidden.html#bitvector_subsubsection", null ],
          [ "How bounded model checking works", "group__module__hidden.html#bmc_subsubsection", null ],
          [ "Where to go from here", "group__module__hidden.html#smt_etc_subsubsection", null ]
        ] ],
        [ "Static analysis", "group__module__hidden.html#static_analysis_section", [
          [ "Abstract Interpretation", "group__module__hidden.html#abstract_interpretation_section", null ]
        ] ]
      ] ],
      [ "Glossary", "group__module__hidden.html#Glossary_section", [
        [ "Instrument", "group__module__hidden.html#instrument_subsection", null ],
        [ "Flattening and Lowering", "group__module__hidden.html#flattening_lowering_subsection", null ],
        [ "Verification Condition", "group__module__hidden.html#verification_condition_subsection", null ]
      ] ],
      [ "Concepts", "group__module__hidden.html#autotoc_md170", [
        [ "Central data structures", "group__module__hidden.html#autotoc_md171", null ],
        [ "{C, java bytecode} &rarr; Parse tree &rarr; Symbol table &rarr; GOTO programs &rarr; GOTO program transformations &rarr; BMC &rarr; counterexample (goto_tracet) &rarr; printing", "group__module__hidden.html#autotoc_md172", null ],
        [ "Instrumentation: goto functions &rarr; goto functions", "group__module__hidden.html#autotoc_md173", null ],
        [ "Goto functions &rarr; BMC &rarr; Counterexample (trace)", "group__module__hidden.html#autotoc_md174", null ],
        [ "Trace &rarr; interpreter &rarr; memory map", "group__module__hidden.html#autotoc_md175", null ],
        [ "Goto functions &rarr; abstract interpretation", "group__module__hidden.html#autotoc_md176", null ],
        [ "Executables (flow of transformations):", "group__module__hidden.html#autotoc_md177", [
          [ "goto-cc", "group__module__hidden.html#autotoc_md178", null ],
          [ "goto-instrument", "group__module__hidden.html#autotoc_md179", null ],
          [ "cbmc", "group__module__hidden.html#autotoc_md180", null ],
          [ "goto-analyzer", "group__module__hidden.html#autotoc_md181", null ]
        ] ],
        [ "Central Data Structures", "group__module__hidden.html#autotoc_md182", [
          [ "GOTO models", "group__module__hidden.html#autotoc_md183", null ],
          [ "goto_functiont", "group__module__hidden.html#autotoc_md184", null ],
          [ "goto_programt", "group__module__hidden.html#autotoc_md185", null ],
          [ "source_locationt", "group__module__hidden.html#autotoc_md186", null ],
          [ "irept", "group__module__hidden.html#autotoc_md187", null ]
        ] ],
        [ "Core Transformation Passes", "group__module__hidden.html#required-transforms", [
          [ "Removal/Lowering of Assembly", "group__module__hidden.html#assembly-transform", null ],
          [ "Linking of Standard Libraries", "group__module__hidden.html#linking-transform", null ],
          [ "Removal/Lowering of Function Pointers", "group__module__hidden.html#function-pointer-transform", null ],
          [ "Memory Mapped IO Instrumentation", "group__module__hidden.html#mmio-transform", null ],
          [ "Instrument/Remove Preconditions", "group__module__hidden.html#precondition-transform", null ],
          [ "Removal/Lowering of Return Statements", "group__module__hidden.html#returns-transform", null ],
          [ "Remove/Lower Vector Typed Expressions", "group__module__hidden.html#vector-transform", null ],
          [ "Remove/Lower Complex Typed Expressions", "group__module__hidden.html#complex-transform", null ],
          [ "Rewrite Unions", "group__module__hidden.html#unions-transform", null ],
          [ "goto_check_c", "group__module__hidden.html#check-c-transform", null ],
          [ "Adjust Float Expressions", "group__module__hidden.html#floats-transform", null ],
          [ "Goto Functions Update", "group__module__hidden.html#update-transform", null ],
          [ "Add Failed Symbols", "group__module__hidden.html#failed-symbols-transform", null ],
          [ "Remove Skip Instructions", "group__module__hidden.html#remove-skip-transform", null ],
          [ "Label Properties", "group__module__hidden.html#properties-transform", null ]
        ] ],
        [ "Optional Transformation Passes", "group__module__hidden.html#optional-transforms", [
          [ "String Instrumentation", "group__module__hidden.html#string-instrument-transform", null ],
          [ "Partial Inlining", "group__module__hidden.html#inlining-transform", null ],
          [ "Transform Assertions Assumptions", "group__module__hidden.html#assertions-transform", null ],
          [ "String Abstraction", "group__module__hidden.html#string-abstraction-transform", null ],
          [ "Add Non-Deterministic Initialisation of Global Scoped Variables", "group__module__hidden.html#nondet-transform", null ],
          [ "Remove Unused Functions", "group__module__hidden.html#unused-functions-transform", null ],
          [ "Add Coverage Goals", "group__module__hidden.html#coverage-transform", null ],
          [ "Slicing", "group__module__hidden.html#slicing-transforms", null ]
        ] ]
      ] ],
      [ "Data structures: core structures and AST", "group__module__hidden.html#data-structures-core-structures-and-ast-section", null ],
      [ "Data structures: from AST to GOTO program", "group__module__hidden.html#data-structures-from-ast-to-goto-program-section", null ],
      [ "Front-end languages: generating codet from multiple languages", "group__module__hidden.html#front-end-languages-generating-codet-from-multiple-languages-section", [
        [ "language_filest, languaget classes:", "group__module__hidden.html#language-uit-section", null ],
        [ "C", "group__module__hidden.html#languages-c-section", null ],
        [ "C++", "group__module__hidden.html#languages-cpp-section", null ],
        [ "Java bytecode", "group__module__hidden.html#languages-java-section", null ]
      ] ],
      [ "Bmct class", "group__module__hidden.html#bmct-class-section", [
        [ "equation", "group__module__hidden.html#equation-section", null ]
      ] ],
      [ "Symbolic executors", "group__module__hidden.html#symbolic-executors-section", [
        [ "Symbolic execution", "group__module__hidden.html#symbolic-execution-section", null ]
      ] ],
      [ "Solvers infrastructure", "group__module__hidden.html#solvers-infrastructure-section", null ],
      [ "Static analysis APIs", "group__module__hidden.html#static-analysis-apis-section", null ],
      [ "Other Tools", "group__module__hidden.html#autotoc_md207", null ],
      [ "CBMC Developer Tutorial", "group__module__hidden.html#cbmc_tutorial", [
        [ "Initial setup", "group__module__hidden.html#autotoc_md200", null ],
        [ "Whirlwind tour of the tools", "group__module__hidden.html#autotoc_md201", [
          [ "Compiling with <span class=\"tt\">goto-cc</span>", "group__module__hidden.html#autotoc_md202", null ],
          [ "Viewing goto-programs", "group__module__hidden.html#autotoc_md203", null ]
        ] ],
        [ "Learning about goto-programs", "group__module__hidden.html#autotoc_md204", [
          [ "First steps with <span class=\"tt\">goto-instrument</span>", "group__module__hidden.html#autotoc_md205", null ],
          [ "Goto-program basics", "group__module__hidden.html#autotoc_md206", null ]
        ] ]
      ] ]
    ] ]
];