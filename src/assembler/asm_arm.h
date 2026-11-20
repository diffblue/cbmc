/*******************************************************************\

Module: Inline assembly: AArch32 instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Instruction semantics for AArch32

#ifndef CPROVER_ASSEMBLER_ASM_ARM_H
#define CPROVER_ASSEMBLER_ASM_ARM_H

#include <memory>

class asm_semanticst;

std::unique_ptr<asm_semanticst> make_asm_arm_semantics();

#endif // CPROVER_ASSEMBLER_ASM_ARM_H
