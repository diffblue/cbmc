/*******************************************************************\

Module: Inline assembly: splitting templates into instructions

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Splitting the template of an inline assembly statement into instructions
/// and their operand tokens, with GCC's `%` operand references resolved to
/// operand indices.

#ifndef CPROVER_ASSEMBLER_ASM_TEMPLATE_H
#define CPROVER_ASSEMBLER_ASM_TEMPLATE_H

#include <util/mp_arith.h>

#include <string>
#include <vector>

class asm_operandst;

/// A token in an operand of an assembly instruction
struct asm_tokent
{
  enum class kindt
  {
    /// a name: register, mnemonic part, condition, symbol
    IDENTIFIER,
    /// a numeric literal, value in `number`
    NUMBER,
    /// a single punctuation character, in `text`
    PUNCTUATION,
    /// a `%N` or `%[name]` reference to operand `index`, with `modifier`
    OPERAND,
    /// a `%lN` or `%l[name]` reference to the C label at `index` of the
    /// statement's label list
    C_LABEL,
    /// a GNU local label reference like `1b` (`backward`) or `1f`
    LOCAL_LABEL,
    /// a string literal, contents in `text`
    STRING
  };

  kindt kind;
  std::string text;
  mp_integer number = 0;
  std::size_t index = 0;
  std::string modifier;
  bool backward = false;

  bool is_punctuation(char c) const
  {
    return kind == kindt::PUNCTUATION && text.size() == 1 && text[0] == c;
  }

  bool is_identifier() const
  {
    return kind == kindt::IDENTIFIER;
  }
};

using asm_token_listt = std::vector<asm_tokent>;

/// One instruction (or directive) of an assembly template
struct asm_instructiont
{
  /// Labels defined right before this instruction, e.g., `1` for `1: ldxr`
  std::vector<std::string> labels;
  /// Instruction prefixes, e.g., `lock` or `rep` on x86 (lower case)
  std::vector<std::string> prefixes;
  /// The mnemonic or directive (lower case); empty for a label-only line
  std::string mnemonic;
  /// The operands, each a list of tokens, split at top-level commas
  std::vector<asm_token_listt> operands;
  /// The source text of the instruction, for diagnostics
  std::string text;

  bool is_directive() const
  {
    return !mnemonic.empty() && mnemonic[0] == '.';
  }
};

/// Architecture-dependent lexical conventions of assembly templates
struct asm_syntaxt
{
  /// Markers that start a comment extending to the end of the line
  std::vector<std::string> line_comments;
  /// Characters that separate statements on one line
  std::string separators = ";";
  /// Characters that, in addition to letters, digits, '_' and '.', may occur
  /// in identifiers
  std::string identifier_characters;
  /// Prefixes that may precede a mnemonic in the same statement
  std::vector<std::string> prefixes;
};

/// Split \p text into instructions.
/// \param text: the assembly template
/// \param syntax: lexical conventions of the architecture
/// \param operands: the statement's operands, used to resolve `%` references;
///   if nullptr the template is basic assembly, where `%` is not special
/// \param [out] instructions: the instructions
/// \param [out] error: a description of the problem if parsing fails
/// \return true on success
bool split_asm_template(
  const std::string &text,
  const asm_syntaxt &syntax,
  const asm_operandst *operands,
  std::vector<asm_instructiont> &instructions,
  std::string &error);

#endif // CPROVER_ASSEMBLER_ASM_TEMPLATE_H
