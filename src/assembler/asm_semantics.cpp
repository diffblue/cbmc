/*******************************************************************\

Module: Inline assembly: instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Architecture-independent parts of the inline assembly semantics

#include "asm_semantics.h"

#include "asm_aarch64.h"
#include "asm_arm.h"
#include "asm_x86.h"

asm_semanticst::constraint_classt asm_semanticst::classify_constraint(
  const std::string &,
  std::size_t &,
  std::string &) const
{
  return constraint_classt::UNKNOWN;
}

std::unique_ptr<asm_semanticst> make_asm_semantics(const irep_idt &arch)
{
  if(arch == "x86_64" || arch == "x32")
    return make_asm_x86_semantics(true);
  else if(arch == "i386")
    return make_asm_x86_semantics(false);
  else if(arch == "arm64")
    return make_asm_aarch64_semantics();
  else if(arch == "arm" || arch == "armel" || arch == "armhf")
    return make_asm_arm_semantics();
  else
    return nullptr;
}
