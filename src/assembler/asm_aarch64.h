/*******************************************************************\

Module: Inline assembly: aarch64 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for aarch64

#ifndef CPROVER_ASSEMBLER_ASM_AARCH64_H
#define CPROVER_ASSEMBLER_ASM_AARCH64_H

#include <memory>

class asm_semanticst;

std::unique_ptr<asm_semanticst> make_asm_aarch64_semantics();

#endif // CPROVER_ASSEMBLER_ASM_AARCH64_H
