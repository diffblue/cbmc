/*******************************************************************\

Module: Inline assembly: the operand interface of GCC-style statements

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The operands, clobbers and labels of a GCC-style inline assembly statement,
/// with their constraints interpreted.

#ifndef CPROVER_ASSEMBLER_ASM_OPERANDS_H
#define CPROVER_ASSEMBLER_ASM_OPERANDS_H

#include <util/expr.h>
#include <util/irep.h>

#include <optional>
#include <set>
#include <string>
#include <vector>

class code_asm_gcct;
class asm_semanticst;

/// One operand of an inline assembly statement
struct asm_operandt
{
  enum class kindt
  {
    /// held in a register: the model uses block-local storage
    REGISTER,
    /// the C lvalue itself, accessed in place
    MEMORY,
    /// a constant
    IMMEDIATE,
    /// an x86 or AArch64 flag output `=@cc<cond>`
    FLAG_OUTPUT
  };

  kindt kind = kindt::REGISTER;
  bool is_output = false;
  /// true for inputs and for `+` outputs
  bool is_read = false;
  /// the symbolic name used in `%[name]`, if any
  irep_idt name;
  std::string constraint;
  /// the C expression; an lvalue for outputs
  exprt expr;
  /// for constraints that name one register, the architecture's name of it
  std::string fixed_register;
  /// for FLAG_OUTPUT: the condition, e.g. "e" for `=@cce`
  std::string flag_condition;
  /// for inputs with a matching constraint: the output they initialise
  std::optional<std::size_t> tied_output;
};

/// The operand interface of a GCC-style inline assembly statement, numbered as
/// GCC numbers them: outputs first, then inputs.
class asm_operandst
{
public:
  std::vector<asm_operandt> operands;
  std::size_t number_of_outputs = 0;
  /// the C labels of `asm goto`, as given in the statement
  std::vector<irep_idt> labels;
  /// the base names of the labels, for `%l[name]`
  std::vector<irep_idt> label_names;
  std::set<std::string> clobbers;
  /// true if the statement has no operand lists at all ("basic asm"), in
  /// which case `%` in the template is not special
  bool is_basic = false;

  bool clobbers_memory() const
  {
    return clobbers.count("memory") != 0;
  }

  /// \return the index of the operand named \p name, if any
  std::optional<std::size_t> find(const irep_idt &name) const;

  /// \return the index of the label with base name \p name, if any
  std::optional<std::size_t> find_label(const irep_idt &name) const;

  /// Interpret the operands of \p code.
  /// \param code: the statement
  /// \param semantics: for architecture-specific constraint letters; may be
  ///   nullptr, in which case only generic letters are understood
  /// \param [out] error: why the operands could not be interpreted
  /// \return true on success
  bool parse(
    const code_asm_gcct &code,
    const asm_semanticst *semantics,
    std::string &error);
};

#endif // CPROVER_ASSEMBLER_ASM_OPERANDS_H
