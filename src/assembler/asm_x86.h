/*******************************************************************\

Module: Inline assembly: x86 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for x86 (i386 and x86-64), AT&T syntax

#ifndef CPROVER_ASSEMBLER_ASM_X86_H
#define CPROVER_ASSEMBLER_ASM_X86_H

#include <memory>

class asm_semanticst;

/// \param x86_64: true for 64-bit registers (x86_64, x32)
std::unique_ptr<asm_semanticst> make_asm_x86_semantics(bool x86_64);

#endif // CPROVER_ASSEMBLER_ASM_X86_H
