/*******************************************************************\

Module: Utilities for building havoc code for expressions.

Author: Saswat Padhi, saspadhi@amazon.com

Date: July 2021

\*******************************************************************/

/// \file
/// Utilities for building havoc code for expressions

#ifndef CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H

#include <set>

#include <goto-programs/goto_program.h>

#include <util/expr_util.h>

typedef std::set<exprt> assignst;

/// \brief A class containing utility functions for havocing expressions.
class havoc_utils_is_constantt : public is_constantt
{
public:
  explicit havoc_utils_is_constantt(const assignst &mod) : assigns(mod)
  {
  }

  bool is_constant(const exprt &expr) const override
  {
    // Besides the "usual" constants (checked in is_constantt::is_constant),
    // we also treat unmodified symbols as constants
    if(expr.id() == ID_symbol && assigns.find(expr) == assigns.end())
      return true;

    return is_constantt::is_constant(expr);
  }

protected:
  const assignst &assigns;
};

class havoc_utilst
{
public:
  explicit havoc_utilst(const assignst &mod) : assigns(mod), is_constant(mod)
  {
  }

  /// \brief Append goto instructions to havoc the full `assigns` set
  ///
  /// This function invokes `append_havoc_code_for_expr` on each expression in
  /// the `assigns` set.
  ///
  /// \param location The source location to annotate on the havoc instruction
  /// \param dest The destination goto program to append the instructions to
  void append_full_havoc_code(
    const source_locationt location,
    goto_programt &dest) const;

  /// \brief Append goto instructions to havoc a single expression `expr`
  ///
  /// If `expr` is an array index or object dereference expression,
  /// with a non-constant offset, e.g. a[i] or *(b+i) with a non-constant `i`,
  /// then instructions are generated to havoc the entire underlying object.
  /// Otherwise, e.g. for a[0] or *(b+i) when `i` is a known constant,
  /// the instructions are generated to only havoc the scalar value of `expr`.
  ///
  /// \param location The source location to annotate on the havoc instruction
  /// \param expr The expression to havoc
  /// \param dest The destination goto program to append the instructions to
  virtual void append_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const;

  /// \brief Append goto instructions to havoc the underlying object of `expr`
  ///
  /// \param location The source location to annotate on the havoc instruction
  /// \param expr The expression to havoc
  /// \param dest The destination goto program to append the instructions to
  virtual void append_object_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const;

  /// \brief Append goto instructions to havoc the value of `expr`
  ///
  /// \param location The source location to annotate on the havoc instruction
  /// \param expr The expression to havoc
  /// \param dest The destination goto program to append the instructions to
  virtual void append_scalar_havoc_code_for_expr(
    const source_locationt location,
    const exprt &expr,
    goto_programt &dest) const;

protected:
  const assignst &assigns;
  const havoc_utils_is_constantt is_constant;
};

#endif // CPROVER_GOTO_INSTRUMENT_HAVOC_UTILS_H
