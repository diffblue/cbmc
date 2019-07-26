/*******************************************************************\

Module: Conversion from Expression or Type to Statement List Language

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#ifndef CPROVER_STATEMENT_LIST_CONVERTERS_EXPR2STATEMENT_LIST_H
#define CPROVER_STATEMENT_LIST_CONVERTERS_EXPR2STATEMENT_LIST_H

#include <util/irep.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <string>

/// Converts a given expression to human-readable STL code.
/// \param expr: Expression to be converted.
/// \param ns: Namespace of the TIA application.
/// \result String with the STL representation of the given parameters.
std::string expr2stl(const exprt &expr, const namespacet &ns);

/// Converts a given type to human-readable STL code.
/// \param type: Type to be converted.
/// \param ns: Namespace of the TIA application.
/// \result String with the STL representation of the given type.
std::string type2stl(const typet &type, const namespacet &ns);

/// Class for saving the internal state of the conversion process.
class expr2stlt
{
  /// Internal representation of the FC bit in STL. Used to track if the
  /// current boolean operation is part of another.
  bool inside_bit_string;

  /// Flag to specify if the next symbol to convert is a reference to a
  /// variable.
  bool is_reference;

  /// Contains the symbol table of the current program to convert.
  const namespacet &ns;

  /// Used for saving intermediate results of the conversion process.
  std::stringstream result;

public:
  /// Creates a new instance of the converter.
  /// \param ns: Namespace containing the symbols of the program to convert.
  explicit expr2stlt(const namespacet &ns);

  /// Invokes the conversion process for the given expression and calls itself
  /// recursively in the process.
  /// \param expr: Expression to convert. Operands of this expression will be
  ///   converted as well via recursion.
  /// \return: String containing human-readable STL code for the expression.
  std::string convert(const exprt &expr);

private:
  /// Converts the given AND expression to human-readable STL code. If the
  /// expression marks the beginning of a bit string, the first non-trivial
  /// operand (that encloses all expressions which are not a symbol or a
  /// negation of a symbol) is being converted first. This reduces nesting.
  /// \param expr: AND expression to convert.
  void convert(const and_exprt &expr);

  /// Converts the given OR expression to human-readable STL code. If the
  /// expression marks the beginning of a bit string, the first non-trivial
  /// operand (that encloses all expressions which are not a symbol or a
  /// negation of a symbol) is being converted first. This reduces nesting.
  /// \param expr: OR expression to convert.
  void convert(const or_exprt &expr);

  /// Converts the given XOR expression to human-readable STL code. If the
  /// expression marks the beginning of a bit string, the first non-trivial
  /// operand (that encloses all expressions which are not a symbol or a
  /// negation of a symbol) is being converted first. This reduces nesting.
  /// \param expr: XOR expression to convert.
  void convert(const xor_exprt &expr);

  /// Converts the given notequal (!=) expression to human-readable STL code.
  /// If the expression marks the beginning of a bit string, the first
  /// non-trivial operand (that encloses all expressions which are not a symbol
  /// or a negation of a symbol) is being converted first. This reduces
  /// nesting.
  /// \param expr: Notequal expression to convert.
  void convert(const notequal_exprt &expr);

  /// Converts the given equal (==) expression to human-readable STL code. If
  /// the expression marks the beginning of a bit string, the first non-trivial
  /// operand (that encloses all expressions which are not a symbol or a
  /// negation of a symbol) is being converted first. This reduces nesting.
  /// \param expr: Equal expression to convert.
  void convert(const equal_exprt &expr);

  /// Converts the given NOT expression to human-readable STL code. This
  /// function may only be called in the case of a new bit string. If the NOT
  /// expression wraps a symbol it is negated and loaded on the RLO via a
  /// simple AN instruction. In the case of a more complex expression, the
  /// expression is being converted first and negated afterwards.
  /// \param expr: Not expression to convert.
  void convert(const not_exprt &expr);

  /// Converts the given symbol expression to human-readable STL code. This
  /// function also checks if the symbol should be a reference and adds the
  /// additional code if needed.
  /// \param expr: Symbol expression to convert.
  void convert(const symbol_exprt &expr);

  /// Iterates through all the given operands and converts them depending on
  /// the operation. Performs a simplification by rearranging the operands
  /// if appropriate.
  /// \param [out] operands: Operands of any multiary instruction.
  /// \param operation: Character specifying the operation in STL.
  void
  convert_multiary_bool(std::vector<exprt> &operands, const char operation);

  /// Iterates through all the given operands and converts them depending on
  /// the operation.
  /// \param operands: Operands of any multiary instruction.
  /// \param operation: Character specifying the operation in STL.
  void convert_multiary_bool_operands(
    const std::vector<exprt> &operands,
    const char operation);

  /// Converts a single boolean operand and introduces an additional nesting
  /// layer if needed.
  void convert_bool_operand(const exprt &op);

  /// Iterates through all the given operands in search for the first
  /// non-trivial operand (that encloses all expressions which are not a symbol
  /// or a negation of a symbol). If found, removes the operand from the list
  /// and converts it first. This is used to avoid unnecessary nesting.
  /// \param [out] operands: List of operands. Gets modified by this function
  ///   if it includes a non-trivial operand.
  void convert_first_non_trivial_operand(std::vector<exprt> &operands);

  /// Returns the given identifier in a form that is compatible with STL by
  /// looking up the symbol or cutting the scope when needed.
  /// \param identifier: Identifier that should be converted.
  /// \return: Converted identifier.
  irep_idt id_shorthand(const irep_idt &identifier);
};

#endif // CPROVER_STATEMENT_LIST_CONVERTERS_EXPR2STATEMENT_LIST_H
