var cprover_documentation =
[
    [ "Versions", "cprover_documentation.html#autotoc_md189", null ],
    [ "Report bugs", "cprover_documentation.html#autotoc_md190", null ],
    [ "Contributing to the code base", "cprover_documentation.html#autotoc_md191", null ],
    [ "License", "cprover_documentation.html#autotoc_md192", null ],
    [ "Overview of Documentation", "cprover_documentation.html#autotoc_md193", null ],
    [ "Memory Bounds Checking", "memory-bounds-checking.html", null ],
    [ "SATABS", "satabs.html", [
      [ "SATABS—Predicate Abstraction with SAT", "satabs.html#man_satabs", [
        [ "For users:", "cprover_documentation.html#autotoc_md194", null ],
        [ "For contributors:", "cprover_documentation.html#autotoc_md195", null ],
        [ "Automatic Program Verification with SATABS", "satabs.html#autotoc_md209", null ],
        [ "Installing SATABS", "satabs.html#man_install-satabs", [
          [ "Requirements", "satabs.html#autotoc_md210", null ],
          [ "Choosing and Installing a Model Checker", "satabs.html#autotoc_md211", null ],
          [ "Installing SATABS", "satabs.html#autotoc_md212", null ],
          [ "Requirements", "satabs.html#autotoc_md213", null ]
        ] ],
        [ "Overview", "satabs.html#man_satabs-overview", [
          [ "Working with Claims", "satabs.html#autotoc_md214", null ]
        ] ],
        [ "Programs that use Libraries", "satabs.html#man_satabs-libraries", null ],
        [ "Unit Testing with SATABS", "satabs.html#man_satabs-unit-test", [
          [ "Further Reading", "satabs.html#autotoc_md215", null ]
        ] ],
        [ "Background", "satabs.html#man_satabs-background", [
          [ "Sound Abstractions", "satabs.html#autotoc_md216", null ],
          [ "Spurious Counterexamples", "satabs.html#autotoc_md217", null ],
          [ "Automatic Refinement", "satabs.html#autotoc_md218", null ]
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
    [ "CBMC Architecture", "cbmc-architecture.html", "cbmc-architecture" ],
    [ "Folder Walkthrough", "folder-walkthrough.html", null ],
    [ "Code Walkthrough", "code-walkthrough.html", [
      [ "Data structures: core structures and AST", "code-walkthrough.html#data-structures-core-structures-and-ast-section", null ],
      [ "Data structures: from AST to GOTO program", "code-walkthrough.html#data-structures-from-ast-to-goto-program-section", null ],
      [ "Front-end languages: generating codet from multiple languages", "code-walkthrough.html#front-end-languages-generating-codet-from-multiple-languages-section", [
        [ "<tt>src/</tt>", "folder-walkthrough.html#autotoc_md184", null ],
        [ "<tt>doc/</tt>", "folder-walkthrough.html#autotoc_md185", null ],
        [ "<tt>regression/</tt>", "folder-walkthrough.html#autotoc_md186", null ],
        [ "<tt>unit/</tt>", "folder-walkthrough.html#autotoc_md187", null ],
        [ "Directory dependencies", "folder-walkthrough.html#autotoc_md188", null ],
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
      [ "Other Tools", "other-tools.html#autotoc_md203", null ]
    ] ],
    [ "Tutorials", "tutorial.html", [
      [ "CBMC Developer Tutorial", "tutorial.html#cbmc_tutorial", [
        [ "Initial setup", "tutorial.html#autotoc_md196", null ],
        [ "Whirlwind tour of the tools", "tutorial.html#autotoc_md197", [
          [ "Compiling with <tt>goto-cc</tt>", "tutorial.html#autotoc_md198", null ],
          [ "Viewing goto-programs", "tutorial.html#autotoc_md199", null ]
        ] ],
        [ "Learning about goto-programs", "tutorial.html#autotoc_md200", [
          [ "First steps with <tt>goto-instrument</tt>", "tutorial.html#autotoc_md201", null ],
          [ "Goto-program basics", "tutorial.html#autotoc_md202", null ]
        ] ]
      ] ]
    ] ]
];