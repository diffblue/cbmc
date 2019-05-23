/*******************************************************************\

Module: String solver

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_STRINGS_EQUATION_SYMBOL_MAPPING_H
#define CPROVER_SOLVERS_STRINGS_EQUATION_SYMBOL_MAPPING_H

#include <map>
#include <unordered_map>

#include <util/expr.h>

/// Maps equation to expressions contained in them and conversely expressions to
/// equations that contain them. This can be used on a subset of expressions
/// which interests us, in particular strings. Equations are identified by an
/// index of type `std::size_t` for more efficient insertion and lookup.
class equation_symbol_mappingt
{
public:
  /// Record the fact that equation `i` contains expression `expr`
  void add(const std::size_t i, const exprt &expr);

  /// \param i: index corresponding to an equation
  /// \return vector of expressions contained in the equation with the given
  ///   index `i`
  std::vector<exprt> find_expressions(const std::size_t i);

  /// \param expr: an expression
  /// \return vector of equations containing the given expression `expr`
  std::vector<std::size_t> find_equations(const exprt &expr);

private:
  /// Record index of the equations that contain a given expression
  std::map<exprt, std::vector<std::size_t>> equations_containing;
  /// Record expressions that are contained in the equation with the given index
  std::unordered_map<std::size_t, std::vector<exprt>> strings_in_equation;
};

#endif // CPROVER_SOLVERS_STRINGS_EQUATION_SYMBOL_MAPPING_H
