/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

/// \file
/// Conversion between exprt and miniBDD

#ifndef CPROVER_SOLVERS_PROP_BDD_EXPR_H
#define CPROVER_SOLVERS_PROP_BDD_EXPR_H

/*! \file solvers/prop/bdd_expr.h
 * \brief Binary decision diagram
 *
 * \author Michael Tautschnig, michael.tautschnig@qmul.ac.uk
 * \date   Sat, 02 Jan 2016 20:26:19 +0100
*/

#include <util/expr.h>

#include <solvers/bdd/bdd.h>

#include <unordered_map>

/// Conversion between \c exprt and \c bbdt
/// This encapsulate a bdd_managert, thus BDDs created with this class should
/// only be combined with BDDs created using the same instance of
/// \ref bdd_exprt .
/// See unit tests in unit/solvers/prop/bdd_expr.cpp for examples.
class bdd_exprt
{
public:
  bddt from_expr(const exprt &expr);
  exprt as_expr(const bddt &root) const;

protected:
  bdd_managert bdd_mgr;

  typedef std::unordered_map<exprt, bddt, irep_hash> expr_mapt;

  expr_mapt expr_map;

  /// Mapping from BDD variables to expressions: the expression at index \c i
  /// of \p node_map corresponds to the i-th variable
  std::vector<exprt> node_map;

  bddt from_expr_rec(const exprt &expr);
  exprt as_expr(
    const bdd_nodet &r,
    std::unordered_map<bdd_nodet::idt, exprt> &cache) const;
};

#endif // CPROVER_SOLVERS_PROP_BDD_EXPR_H
