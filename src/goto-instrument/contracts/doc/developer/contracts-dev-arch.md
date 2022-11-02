# Code Contracts Software Architecture {#contracts-dev-arch}

Back to @ref contracts-dev

@tableofcontents

## Architecture Overview

The code implementing @ref contracts-dev-spec is found in @ref dfcc-module

We go over each class and explain how it works in relation to others.

The @ref dfcct class is the main entry point into the transformation.

The method @ref dfcct#transform_goto_model first separates the functions of the goto model in different groups (functions to instrument, pure contract symbols from which to generate code, functions to check against contracts, functions to replace with contracts) and applies the transformation
to the whole goto model, by scheduling the translation passes
described in @ref contracts-dev-spec :

1. @ref contracts-dev-spec-codegen is applied to all contracts to check or replace;
2. @ref contracts-dev-spec-dfcc is applied to all library or user-defined goto functions;
3. @ref contracts-dev-spec-harness is applied to the harness function;
4. @ref contracts-dev-spec-contract-checking is applied to the function to be checked against a contract;
5. @ref contracts-dev-spec-contract-replacement is applied to each function to be replaced by a contract;

Each of these translation passes is implemented in a specific class:

 Class                           | Specification
 :-------------------------------|:---------------------------------------
 @ref dfcc_instrumentt           | Implements @ref contracts-dev-spec-dfcc for @ref goto_functiont, @ref goto_programt, or subsequences of instructions of @ref goto_programt
 @ref dfcc_is_fresht             | Implements @ref contracts-dev-spec-is-fresh
 @ref dfcc_is_freeablet          | Implements @ref contracts-dev-spec-is-freeable
 @ref dfcc_spec_functionst       | Implements @ref contracts-dev-spec-spec-rewriting
 @ref dfcc_wrapper_programt  | Implements @ref contracts-dev-spec-contract-checking for contracts
 ^                               | Implements @ref contracts-dev-spec-contract-replacement for contracts
 @ref dfcc_contract_handlert | Implements @ref contracts-dev-spec-codegen for contracts
 ^                               | Implements the interface @ref dfcc_contract_handlert for contract by delegating operations to @ref dfcc_wrapper_programt
 @ref dfcc_swap_and_wrapt        | Implements @ref contracts-dev-spec-contract-checking by delegating basic operations to @ref dfcc_contract_handlert
 ^                               | Implements @ref contracts-dev-spec-contract-replacement by delegating basic operations to @ref dfcc_contract_handlert
 ^                               | Implements @ref contracts-dev-spec-contract-checking-rec by delegating basic operations to @ref dfcc_contract_handlert

The following classes contain utility methods:
- @ref dfcc_utilst : Provides basic utility methods to the other classes such as
  locating a function symbol, adding a parameter to a function symbol, cloning
  or renaming a function symbol, creating fresh symbols, inlining a function
  body, etc.
- @ref dfcc_libraryt : Provides a C++ interface to access C library functions
  defined in @ref cprover_contracts.c. Using this class it is possible to load
  the library symbols and post-process them with loop unrolling or inlining, etc.
