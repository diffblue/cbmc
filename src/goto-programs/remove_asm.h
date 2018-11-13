/*******************************************************************\

Module: Remove 'asm' statements by compiling them into suitable
        standard goto program instructions

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

/// \file
/// Remove 'asm' statements by compiling them into suitable standard goto
/// program instructions

/// Inline assembly statements in the source program (in either gcc- or
/// msc-style) are represented by instructions of kind `OTHER` with a `code`
/// member of type `code_asmt` in the goto program.
///
/// For example, the gcc inline assembly statement below
///
/// ```
/// int input = 1;
/// int result;
///
/// asm volatile (
///   "mov %1, %0; add $1, %0"
///   : "=r" (result)
///   : "r" (input)
///   : "cc");
/// ```
///
/// would be represented by a `code_asmt` statement with `op0()` being the
/// string literal "mov %1, %0; add $1, %0" (as a `string_constantt` expression)
/// and `op1()`, `op2()`, and `op3()`, respectively, containing the output list,
/// input list, and clobbered registers.
///
/// The `remove_asm()` function replaces the inline assembly statements in a
/// given goto program with appropriate (sequences of) non-assembly goto program
/// instructions.
///
/// It first parses the assembly instructions string (via `assembler_parsert`)
/// and inspects the input/output/clobber lists. Then, it generates a sequence
/// of goto program instructions that either directly implement the assembly
/// instructions, or call a suitable library function (see
/// `library/x86_assembler.c`).
///
/// At present only a small number of x86 and Power instructions are supported.
/// Unrecognised assembly instructions are ignored (i.e., they are simply
/// removed from the goto program).

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H

#include <goto-programs/goto_functions.h>

class goto_modelt;
class symbol_tablet;

void remove_asm(goto_functionst &, symbol_tablet &);

void remove_asm(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_ASM_H
