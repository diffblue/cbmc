# AGENTS.md - Guide for AI Coding Assistants

This document is designed to help AI coding assistants (Kiro, Claude Code,
Copilot, etc.) effectively work with the CBMC codebase. It provides a
comprehensive overview of the project structure, key concepts, and development
practices.

## Table of Contents

1. [Project Overview](#project-overview)
2. [Repository Structure](#repository-structure)
3. [Key Directories](#key-directories)
4. [Architectural Concepts](#architectural-concepts)
5. [Central Data Structures](#central-data-structures)
6. [Build System](#build-system)
7. [Testing Framework](#testing-framework)
8. [Coding Standards](#coding-standards)
9. [Documentation Practices](#documentation-practices)
10. [Common Development Workflows](#common-development-workflows)
11. [Navigation Tips](#navigation-tips)
12. [Important Links](#important-links)

---

## Project Overview

**CBMC** (C Bounded Model Checker) is the main tool in the CProver suite for
formal verification of C and C++ programs.

### What CBMC Does
- Bounded model checking for C/C++ programs
- Supports C89, C99, most of C11, C17, C23
- Supports most compiler extensions from gcc and Visual Studio
- Verifies array bounds, pointer safety, exceptions, and user-specified
  assertions
- Performs verification by unwinding loops and passing equations to decision
  procedures
- Also includes **JBMC** for Java bytecode verification

### Project Website
- Main site: [cprover.org](http://www.cprover.org/cbmc)
- Documentation: [diffblue.github.io/cbmc](https://diffblue.github.io/cbmc/)

---

## Repository Structure

```
cbmc/
├── src/                    # Main source code
├── jbmc/                   # Java Bounded Model Checker
├── regression/             # Regression test suites
├── unit/                   # Unit test suites
├── doc/                    # Documentation
│   ├── architectural/      # Architecture documentation
│   ├── ADR/                # Architecture Decision Records
│   ├── cprover-manual/     # User manual
│   └── man/                # Man pages
├── scripts/                # Build and development scripts
├── cmake/                  # CMake configuration
├── integration/            # Integration test examples
│   ├── linux/              # Linux integration examples
│   └── xen/                # Xen hypervisor examples
├── .github/                # GitHub configuration and workflows
│   ├── workflows/          # CI/CD workflow definitions
│   │   ├── build-and-test-Linux.yaml    # Main Linux build and test
│   │   ├── pull-request-checks.yaml     # PR validation checks
│   │   ├── coverage.yaml                # Code coverage reporting
│   │   ├── syntax-checks.yaml           # Code style and linting
│   │   ├── codeql-analysis.yml          # Security analysis
│   │   ├── performance.yaml             # Performance benchmarking
│   │   ├── profiling.yaml               # Pre-solver profiling on PRs
│   │   └── release-packages.yaml        # Release automation
│   └── dependabot.yml      # Dependency update automation
├── CODING_STANDARD.md      # Coding conventions
├── COMPILING.md            # Build instructions
├── TOOLS_OVERVIEW.md       # Overview of all tools
└── README.md               # Main readme
```

---

## Key Directories

### `src/` - Main Source Code

The source is organized into modular directories by functionality:

#### **Core Components**

- **`util/`** - Fundamental utilities and data structures
  - Base data structures like `irept`, `exprt`, `typet`
  - String handling, expression utilities
  - Foundation for everything else

- **`goto-programs/`** - GOTO intermediate representation
  - Core IR data structures: `goto_programt`, `goto_functiont`, `goto_modelt`
  - The heart of CBMC's program representation

- **`linking/`** - Linking GOTO programs together
  - Combines multiple GOTO programs

- **`big-int/`** - Big integer arithmetic
  - Arbitrary precision integer operations
  - Used throughout CBMC for large numeric computations

#### **Language Front Ends**

- **`langapi/`** - Language API interface
  - Abstract interface for language front-ends

- **`ansi-c/`** - C language front-end
  - Parsing and type-checking for C

- **`cpp/`** - C++ language front-end
  - C++ specific parsing (depends on `ansi-c`)

#### **Analysis and Verification**

- **`goto-symex/`** - Symbolic execution engine
  - Core symbolic execution implementation
  - Transforms GOTO programs into logical formulas

- **`analyses/`** - Static analyses
  - Various static analysis passes
  - Abstract interpretation implementations

- **`pointer-analysis/`** - Pointer analysis
  - Points-to analysis and pointer tracking

- **`goto-checker/`** - Verification orchestration
  - Coordinates the verification process

#### **Solvers**

- **`solvers/`** - Decision procedures
  - SAT/SMT solver interfaces
  - Bit-blasting and encoding

#### **Tools (Executables)**

- **`cbmc/`** - Main CBMC tool
- **`goto-cc/`** - Compiler wrapper
- **`goto-instrument/`** - Program instrumentation
- **`goto-analyzer/`** - Abstract interpretation tool
- **`goto-diff/`** - Diff tool for GOTO programs
- **`goto-harness/`** - Test harness generation
- **`goto-bmc/`** - Bounded model checking
- **`memory-analyzer/`** - Memory analysis with gdb
- **`symtab2gb/`** - Symbol table to GOTO binary

#### **Other Components**

- **`json/`** - JSON handling
- **`xmllang/`** - XML support
- **`assembler/`** - Assembly support

### `jbmc/` - Java Bounded Model Checker

Parallel structure to main CBMC for Java:

- **`jbmc/src/`** - Java-specific source code
  - **`java_bytecode/`** - Java bytecode front-end
    - Parsing and analysis of Java .class files
    - Java-specific type system and language features
    - JVM instruction handling
  - **`jbmc/`** - Main JBMC tool executable
    - Entry point for Java verification
  - **`janalyzer/`** - Java static analyzer
    - Abstract interpretation for Java
  - **`jdiff/`** - Diff tool for Java programs
    - Comparison of Java GOTO programs
  - **`miniz/`** - ZIP compression library
    - Used for reading JAR files and compressed class files
- **`jbmc/regression/`** - Java regression tests
- **`jbmc/unit/`** - Java unit tests

### `regression/` - Regression Tests

Extensive test suites organized by tool and feature:
- **`cbmc/`** - Main CBMC tests
- **`goto-instrument/`** - Instrumentation tests
- **`goto-analyzer/`** - Analysis tests
- **`contracts/`** - Contract tests
- **`cbmc-cpp/`** - C++ specific tests
- **`smt2_solver/`** - SMT solver tests
- Many more specialized test directories

See `regression/README.md` for test tags and categories.

### `unit/` - Unit Tests

Unit tests using the Catch framework:
- Organized by module matching `src/` structure
- Tests for individual components and utilities
- Run with `unit` executable

### `doc/` - Documentation

- **`architectural/`** - Architecture documentation
  - `background-concepts.md` - Key concepts
  - `cbmc-architecture.md` - High-level architecture
  - `central-data-structures.md` - Core data structures
  - `folder-walkthrough.md` - Directory guide
  - `goto-program-transformations.md` - Instrumentation passes

- **`ADR/`** - Architecture Decision Records
  - Documents key architectural decisions
  - Useful for understanding design rationale

- **`cprover-manual/`** - User manual
- **`man/`** - Man pages for tools

### `scripts/` - Development Scripts

- Build helpers and utilities
- `cpplint.py` - Style checker
- `profile_cbmc.py` - Performance profiling tool (see [Profiling CBMC](#6-profiling-cbmc))
- `profiling/` - Profiling package (analysis, benchmarks, runner, utils)
- `test.pl` - Regression test runner (in `regression/`)
- CI/CD related scripts

---

## Architectural Concepts

### CBMC Pipeline

CBMC follows a compiler-like architecture with these stages:

```
Source Code → Preprocessing → Parsing → Type Checking
    ↓
Goto Conversion
    ↓
Goto Program (IR)
    ↓
Instrumentation/Transformations
    ↓
Symbolic Execution
    ↓
SAT/SMT Encoding
    ↓
Decision Procedure
    ↓
Counterexample/Trace
```

### GOTO Programs

The **GOTO program** is CBMC's intermediate representation (IR):
- Language-agnostic representation of programs
- Similar to control flow graphs (CFGs)
- Can be saved to "goto binaries" (by `goto-cc`)
- Processed by all back-end tools

### Key Concepts

1. **Symbol Table** - Maps identifiers to their definitions
2. **GOTO Functions** - Collection of functions in IR form
3. **GOTO Instructions** - Individual instructions with guards and types
4. **Symbolic Execution** - Explores program paths symbolically
5. **Bounded Model Checking** - Unwinds loops to finite depth
6. **Decision Procedures** - SAT/SMT solvers that check satisfiability

---

## Central Data Structures

### `goto_modelt`

The top-level data structure representing a complete program:

```cpp
class goto_modelt {
  symbol_tablet symbol_table;      // All symbols (variables, functions, types)
  goto_functionst goto_functions;  // All functions in GOTO form
};
```

### `goto_functionst`

A map from function names to function definitions:

```cpp
// Conceptually: map<identifier, goto_functiont>
```

### `goto_functiont`

Represents a single function:

```cpp
class goto_functiont {
  goto_programt body;                    // Function body (instruction sequence)
  std::vector<irep_idt> parameter_identifiers;  // Parameter names
};
```

### `goto_programt`

A sequence of GOTO instructions forming a function body:

```cpp
class goto_programt {
  std::list<instructiont> instructions;  // Ordered list of instructions
};
```

See `src/goto-programs/goto_program.h` for details.

### `goto_instructiont`

A single instruction in the GOTO program:

```cpp
class goto_instructiont {
  goto_program_instruction_typet type;  // Instruction type (ASSIGN, GOTO, etc.)
  codet code;                           // The actual code/statement
  exprt guard;                          // Boolean condition (optional)
  source_locationt source_location;     // Original source location
  // ... and other fields
};
```

**Instruction Types** include:
- `ASSIGN` - Assignment
- `FUNCTION_CALL` - Function call
- `RETURN` - Return statement
- `GOTO` - Conditional/unconditional jump
- `ASSUME` - Assumption (path constraint)
- `ASSERT` - Assertion to verify
- `SKIP` - No-op
- And more...

### `symbolt`

Represents a symbol (variable, function, type):

```cpp
class symbolt {
  irep_idt name;        // Unique identifier
  typet type;           // Type of symbol
  exprt value;          // Initial value (if applicable)
  source_locationt location;
  // ... other metadata
};
```

### `irept` - The Foundation

The base data structure for most CBMC types:

```cpp
class irept {
  // Tree structure with:
  // - An ID (string)
  // - Named sub-trees (map)
  // - Ordered sub-trees (vector)
};
```

**Key classes built on `irept`:**
- `exprt` - Expressions
- `typet` - Types
- `codet` - Code/statements
- `source_locationt` - Source locations

**Important:** Use the specific subclass methods rather than raw `irept` access.

### `exprt` and `typet`

- **`exprt`** - Represents expressions (operators, literals, variables, etc.)
- **`typet`** - Represents types (int, pointer, array, struct, etc.)

Both inherit from `irept` and provide type-safe accessors.

### Directory Dependencies

Key dependency relationships:
- Tools (cbmc, goto-cc, etc.) → goto-instrument → goto-symex
- goto-symex → solvers, pointer-analysis
- Languages (cpp, ansi-c) → langapi → goto-programs
- Almost everything → util
- util → big-int

See `doc/architectural/folder-walkthrough.md` for the full dependency graph.

---

## Build System

### Build Dependencies

CBMC requires `bison`, `flex`, a C- and C++ compiler, and `make` or `CMake`. To
speed up rebuilds, install `ccache`.

### CMake Build (Recommended)

CBMC uses **CMake 3.8+** as the primary build system.

#### Quick Start

```bash
# 1. Update submodules
git submodule update --init

# 2. Generate build files
cmake -S . -Bbuild

# 3. Build
cmake --build build --parallel $(nproc)

# 4. Run tests
ctest --test-dir build -V -L CORE
```

#### Configuration Options

```bash
# Use specific compiler
cmake -S . -Bbuild -DCMAKE_CXX_COMPILER=clang++

# Build with different SAT solver
cmake -S . -Bbuild -Dsat_impl=cadical

# Debug build
cmake -S . -Bbuild -DCMAKE_BUILD_TYPE=Debug

# Release build
cmake -S . -Bbuild -DCMAKE_BUILD_TYPE=Release
```

#### Build Locations

After building, executables are in:
- `build/bin/` - Main executables (cbmc, goto-cc, etc.)
- `build/lib/` - Libraries

### Makefile Build (Alternative)

Traditional makefiles are also available:

```bash
cd src
make minisat2-download
make -j$(nproc)  # Parallel build
```

Configuration in `src/config.inc` (SAT solver paths, etc.).

### SAT Solver Integration
CBMC can use various SAT/SMT solvers:
- **MiniSat** (default)
- **CaDiCaL**
- **Glucose**
- **Z3**
- And others

CMake automatically downloads MiniSat during configuration.
See `COMPILING.md` for detailed build instructions for all platforms.

---

## Testing Framework

### Regression Tests

Location: `regression/`

#### Running Regression Tests

```bash
# Run all regression tests
make -C regression test

# Run specific test directory
cd regression/cbmc
make test

# Using CMake
ctest --test-dir build -V -L CORE -j$(nproc)
```

#### Test Structure

Each test directory contains:
- Test cases (`.c`, `.cpp`, `.java` files)
- Test descriptor (`test.desc`) with flags (see `regression/test.pl --help` for
  format details)

#### Test Tags

Important tags (see `regression/README.md`):
- `smt-backend` - Requires SMT backend
- `broken-smt-backend` - Known issues with SMT
- `thorough-smt-backend` - Too slow for CI
- Similar tags for specific solvers

### Unit Tests

Location: `unit/`

#### Running Unit Tests

```bash
# Build and run all unit tests
make -C unit test

# Using CMake
cmake --build build --target unit
cd unit && ../build/bin/unit

# Run specific test suite
cd unit && ../build/bin/unit "[solvers]"  # Run only solver tests
```

#### Test Framework

- Uses **Catch2** testing framework
- Tests organized by module
- Each test is a `TEST_CASE` or `SCENARIO`

### Writing Tests

**Regression Test Example:**
```bash
# In regression/cbmc/my-test/
main.c              # Test input
test.desc           # Test configuration
```

**test.desc format:**
```
CORE
main.c
--bounds-check --unwind 5
^VERIFICATION SUCCESSFUL$
```

**Unit Test Example:**
```cpp
TEST_CASE("My feature test", "[my-module]")
{
  // Setup
  // Test
  REQUIRE(result == expected);
}
```

---

## Coding Standards

CBMC follows strict coding standards documented in `CODING_STANDARD.md`.

### Formatting

**Enforced by clang-format** - Run before committing!

Key rules:
- **2 spaces** for indentation (no tabs)
- **80 character** line limit
- Matching `{ }` in same column (except initializers/lambdas)
- Spaces around binary operators (`=`, `+`, `==`)
- Space after comma and colon (in for loops)
- `*`/`&` attached to variable name: `int *ptr;`
- No trailing whitespace
- Newline at end of file

### Control Flow

```cpp
// Correct
if(condition)
{
  do_something();
}
else
{
  do_other();
}

// Single-line blocks (allowed)
if(condition)
  do_something();

// For loops
for(int i = 0; i < n; i++)
{
  // body
}
```

### Comments and Documentation

- **No `/* */` style comments** (use `//` instead)
- **Every file** must start with author comment and `\file` Doxygen tag

```cpp
/// \file
/// Brief description of this file's purpose
```

- **Document all classes, functions, and non-obvious members**

```cpp
/// Brief description ending with period. Longer description can follow.
/// \param arg: Description of parameter
/// \param [out] result: Output parameter description
/// \param [in,out] state: In-out parameter description
/// \return Description of return value
int my_function(int arg, int &result, state_t &state);
```

### Code Organization

- **Methods > 50 lines** should be broken into smaller functions
- Use blank lines to separate logical blocks
- Prefer clear variable names over comments
- **Type safety**: Use proper const-correctness
- **Error handling**: Use descriptive INVARIANT messages

### Interface Stability

- Consider impact on external users
- Public interfaces should be stable
- Document deprecations clearly
- Interfaces = anything used outside a single directory

### Best Practices

1. **Const-correctness** - Mark const what should be const
2. **Type safety** - Avoid casts when possible
3. **Error handling** - Use INVARIANT/PRECONDITION/POSTCONDITION
4. **Documentation** - Prioritize readability
5. **Testing** - Include regression tests for changes

---

## Documentation Practices

### Doxygen Documentation

CBMC uses **Doxygen** for API documentation.

#### Building Documentation

```bash
cd src
doxygen
# Output in doc/html/
```

#### Documentation Style

Follow **LLVM guidelines** with extensions:

```cpp
/// This is the brief description (first sentence).
///
/// More detailed explanation can follow in subsequent paragraphs.
/// Feel free to break into multiple paragraphs for readability.
///
/// \param param1: Short description
/// \param param2: Longer description that needs multiple lines.
///   Additional lines indented by two spaces for clarity.
/// \param [out] output: This parameter is modified by the function
/// \return Description of return value
```

### Documentation Types

1. **File documentation** - Every `.cpp` and `.h` file
2. **Class documentation** - Purpose and usage
3. **Function documentation** - Parameters, return values, behavior
4. **Complex algorithms** - Explain the approach
5. **Non-obvious code** - Clarify intent

### Existing Documentation

Read before coding:
- `CODING_STANDARD.md` - Style and conventions
- `COMPILING.md` - Build instructions
- `TOOLS_OVERVIEW.md` - Tool descriptions
- `doc/architectural/` - Architecture deep-dives
- `doc/ADR/` - Design decisions
- Doxygen output - API reference

---

## Common Development Workflows

### 1. Making Changes to Source Code

```bash
# 1. Create a feature branch from develop
git checkout develop
git checkout -b feature/my-improvement

# 2. Make changes following coding standards
# Edit files in src/

# 3. Format code
# (clang-format is enforced in CI)

# 4. Build
cmake --build build

# 5. Run relevant tests
ctest --test-dir build -V -L CORE -R <relevant-module>
cd unit && ../build/bin/unit "[relevant-module]"

# 6. Commit with clear message
git commit -m "Add feature X to improve Y (explains WHAT)" -m "Doing X is important, because ... (explain WHY and possibly HOW)"

# 7. Push and create PR targeting develop
git push origin feature/my-improvement
```

### 2. Adding a New Feature

```bash
# 1. Implement the feature in appropriate src/ directory
# 2. Add unit tests in unit/
# 3. Add regression tests in regression/
# 4. Update documentation if needed
# 5. Ensure all tests pass
# 6. Create PR with detailed description
```

### 3. Fixing a Bug

```bash
# 1. Create regression test that reproduces the bug
# 2. Confirm test fails with current code
# 3. Fix the bug
# 4. Confirm test now passes
# 5. Ensure no other tests break
# 6. Create PR referencing the issue
```

### 4. Working with GOTO Programs

```bash
# Generate GOTO binary from C code
goto-cc -o program.gb program.c
# View GOTO program
goto-instrument --show-goto-functions program.gb

# Instrument GOTO program
goto-instrument --bounds-check program.gb instrumented.gb

# Verify with CBMC
cbmc instrumented.gb
```

### 5. Running Specific Regression Tests

```bash
# Single test
cd regression/cbmc
../test.pl -C -p -c ../../../src/cbmc/cbmc my-test

# All tests in a category
cd regression/cbmc
make test
```

### 6. Profiling CBMC

The profiling tool (`scripts/profile_cbmc.py`) profiles CBMC's pre-solver
stages using `perf` and generates flamegraphs. Solver time is excluded by
default so results reflect only CBMC's own code.

**Prerequisites:** Linux with `perf` installed.

```bash
# Profile a single file
scripts/profile_cbmc.py test.c -- --bounds-check --unwind 100

# Run 3 built-in benchmarks (linked_list, array_ops, structs)
scripts/profile_cbmc.py --auto

# Extended suite (10 benchmarks) plus CSmith-generated tests
scripts/profile_cbmc.py --auto-large --auto-csmith

# Multiple runs for statistical significance (reports mean ± stddev)
scripts/profile_cbmc.py --auto --runs 3

# Source-level call site resolution (build a debug binary first)
cmake -S . -Bbuild-debug -DCMAKE_BUILD_TYPE=RelWithDebInfo -DWITH_JBMC=OFF
cmake --build build-debug --target cbmc -j$(nproc)
scripts/profile_cbmc.py --auto --debug-binary build-debug/bin/cbmc

# Differential profiling: compare two git refs
scripts/profile_cbmc.py --diff develop my-optimization-branch
```

**Outputs** (in `profile-results/` by default):
- `flamegraph.svg` per benchmark - Interactive flamegraph
- `aggregated.svg` - Combined flamegraph across all benchmarks
- `summary.txt` - Text summary with hotspot analysis and optimization suggestions
- `results.json` - Machine-readable results

**CI integration:** The `profiling.yaml` workflow runs `--auto --runs 3` on
every PR, posts the summary to the GitHub step summary, and uploads
flamegraph SVGs as downloadable artifacts.

---

## Navigation Tips

### Finding Code

**By Functionality:**
- Parsing C code → `src/ansi-c/`
- Symbolic execution → `src/goto-symex/`
- SAT/SMT solvers → `src/solvers/`
- Main CBMC tool → `src/cbmc/`
- Instrumentation → `src/goto-instrument/`

**By Data Structure:**
- GOTO programs → `src/goto-programs/goto_program.h`
- Expressions → `src/util/std_expr.h`, `src/util/expr.h`
- Types → `src/util/type.h`, `src/util/std_types.h`
- Symbols → `src/util/symbol.h`
- Symbol table → `src/util/symbol_table.h`

**By Concept:**
- Loop unwinding → `src/goto-symex/` and `src/goto-instrument/`
- Pointer analysis → `src/pointer-analysis/`
- Static analysis → `src/analyses/`
- Abstract interpretation → `src/analyses/`

### Using grep/ag/ripgrep

```bash
# Find where a class is defined
rg "class goto_programt" src/

# Find usages of a function
rg "goto_convert\(" src/

# Find test cases for a feature
rg "bounds.check" regression/ -l

# Find documentation
rg "\\page" doc/ -A 5
```

### Understanding Module Dependencies

Each source directory has `module_dependencies.txt`:

```bash
# Check what a module depends on
cat src/goto-symex/module_dependencies.txt
```

### Following the Data Flow

To understand how data flows through CBMC:

1. **Start** - Source code input
2. **Frontend** - `src/ansi-c/` or `src/cpp/` parses to AST
3. **Type Checking** - Language-specific type checking
4. **Symbol Table** - Symbols populated in `symbol_tablet`
5. **GOTO Conversion** - AST → `goto_programt`
6. **Goto Model** - Complete `goto_modelt` created
7. **Instrumentation** - `goto-instrument` transforms
8. **Symbolic Execution** - `goto-symex` explores paths
9. **Solver** - SAT/SMT solver in `src/solvers/`
10. **Result** - Verification result or counterexample

### Reading the Code

**Start with:**
1. `src/cbmc/cbmc_parse_options.cpp` - Entry point for CBMC
2. `src/util/irep.h` - Core data structure of all intermediate representations
3. Headers in `src/goto-programs/` - Core IR structures
4. `doc/architectural/` - Architecture documentation

**Understand patterns:**
- Most data structures inherit from `irept`
- Use `id2string()` to convert `irep_idt` to `std::string`
- Expression/type casting with `expr_cast.h`
- Visitors for traversing expressions/instructions

---

## Important Links

### Documentation
- [CProver Documentation](https://diffblue.github.io/cbmc/) - Complete developer docs
- [CBMC Architecture](https://diffblue.github.io/cbmc/cbmc-architecture.html) - High-level overview
- [Background Concepts](https://diffblue.github.io/cbmc/background-concepts.html) - Key concepts
- [Developer Tutorial](https://diffblue.github.io/cbmc/tutorial.html) - Getting started

### In This Repository
- [CODING_STANDARD.md](CODING_STANDARD.md) - Coding conventions
- [COMPILING.md](COMPILING.md) - Build instructions
- [TOOLS_OVERVIEW.md](TOOLS_OVERVIEW.md) - All tools explained
- [FEATURE_IDEAS.md](FEATURE_IDEAS.md) - Mini-projects for contributors
- [README.md](README.md) - Main readme

### Architecture Documentation
- [doc/architectural/folder-walkthrough.md](doc/architectural/folder-walkthrough.md) - Directory structure
- [doc/architectural/central-data-structures.md](doc/architectural/central-data-structures.md) - Core data structures
- [doc/architectural/goto-program-transformations.md](doc/architectural/goto-program-transformations.md) - Instrumentation passes
- [doc/architectural/compilation-and-development.md](doc/architectural/compilation-and-development.md) - Development guide

### Architecture Decision Records (ADRs)
- [doc/ADR/](doc/ADR/) - Design decisions
- [doc/ADR/cpp_api_modularisation.md](doc/ADR/cpp_api_modularisation.md) - API design
- [doc/ADR/symex_ready_goto.md](doc/ADR/symex_ready_goto.md) - Symex design

### External Resources
- [Main Website](http://www.cprover.org/cbmc) - User documentation
- [GitHub Repository](https://github.com/diffblue/cbmc) - Public repository
- [CProver Manual](http://www.cprover.org/cprover-manual/) - User manual

---

## Quick Reference Card

### Common Tasks

| Task | Command |
|------|---------|
| Build everything | `cmake --build build` |
| Build CBMC only | `cmake --build build --target cbmc` |
| Run all tests | `ctest --test-dir build -V -L CORE -j$(nproc)` |
| Run unit tests | `cd unit && ../build/bin/unit` |
| Format code | `clang-format -i <file>` |
| Generate docs | `cd src && doxygen` |
| Create GOTO binary | `goto-cc -o out.gb input.c` |
| View GOTO program | `goto-instrument --show-goto-functions prog.gb` |
| Run CBMC | `cbmc program.gb` or `cbmc program.c` |
| Profile CBMC | `scripts/profile_cbmc.py --auto --runs 3` |

### Key Files to Know

- `src/goto-programs/goto_program.h` - Core IR structures
- `src/util/irep.h` - Base data structure
- `src/util/expr.h` - Expressions
- `src/util/type.h` - Types
- `src/util/symbol.h` - Symbols
- `src/goto-symex/goto_symext.h` - Symbolic execution
- `src/solvers/` - SAT/SMT interfaces

### Module Map (Key Dependencies)

```
cbmc → goto-instrument → goto-symex → {solvers, pointer-analysis}
goto-cc → cpp → ansi-c → langapi → goto-programs
goto-programs → util → big-int
```

---

## Tips for AI Assistants

### When Adding Features
1. Check existing patterns in similar code
2. Follow the module structure (don't cross module boundaries unnecessarily)
3. Add tests (unit and regression)
4. Update documentation
5. Follow coding standards (formatting, comments)

### When Debugging
1. Check if there's a regression test that demonstrates the issue
2. Use `goto-instrument --show-goto-functions` to inspect IR
3. Look for similar fixed bugs in git history
4. Check module dependencies if getting linker errors

### When Refactoring
1. Understand data flow first (see Navigation Tips)
2. Check impact on public interfaces
3. Run full test suite
4. Update documentation

### Common Pitfalls
- Don't break 80-char line limit (enforced by CI)
- Don't use `/* */` comments
- Don't forget Doxygen comments on public interfaces
- Don't skip regression tests
- Don't modify `irept` directly; use subclass accessors
- Don't forget to update submodules after pulling

### Understanding Output
- CBMC outputs verification results and traces
- Traces show path through program leading to property violation
- Check `source_locationt` in instructions for source mapping

---

**Last Updated:** 2026-01-19

This guide is maintained to help AI coding assistants work effectively with
CBMC. For questions or updates, refer to the main documentation or ask the
development team.
