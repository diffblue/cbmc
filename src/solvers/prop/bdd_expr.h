/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

#ifndef CPROVER_SOLVERS_PROP_BDD_EXPR_H
#define CPROVER_SOLVERS_PROP_BDD_EXPR_H

/*! \file solvers/prop/bdd_expr.h
 * \brief Binary decision diagram
 *
 * \author Michael Tautschnig, michael.tautschnig@qmul.ac.uk
 * \date   Sat, 02 Jan 2016 20:26:19 +0100
*/

#include <util/expr.h>

#include <solvers/miniBDD/miniBDD.h>

class namespacet;

/*! \brief TO_BE_DOCUMENTED
*/
class bdd_exprt
{
public:
  bdd_exprt(const namespacet &_ns):ns(_ns) { }

  void from_expr(const exprt &expr);
  exprt as_expr() const;

protected:
  const namespacet &ns;
  mini_bdd_mgrt bdd_mgr;
  mini_bddt root;

  typedef std::unordered_map<exprt, mini_bddt, irep_hash> expr_mapt;
  expr_mapt expr_map;
  typedef std::map<unsigned, exprt> node_mapt;
  node_mapt node_map;

  mini_bddt from_expr_rec(const exprt &expr);
  exprt as_expr(const mini_bddt &r) const;
};

#endif // CPROVER_SOLVERS_PROP_BDD_EXPR_H
