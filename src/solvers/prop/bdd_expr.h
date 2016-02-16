/*******************************************************************\

Module: Conversion between exprt and miniBDD

Author: Michael Tautschnig, michael.tautschnig@qmul.ac.uk

\*******************************************************************/

#ifndef CPROVER_MINI_BDD_EXPR_H
#define CPROVER_MINI_BDD_EXPR_H

/*! \file util/bdd_expr.h
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

  typedef miniBDD::BDD BDDt;

protected:
  const namespacet &ns;
  miniBDD::mgr bdd_mgr;  
  BDDt root;

  typedef hash_map_cont<exprt, BDDt, irep_hash> expr_mapt;
  expr_mapt expr_map;
  typedef std::map<unsigned, exprt> node_mapt;
  node_mapt node_map;

  BDDt from_expr_rec(const exprt &expr);
  exprt as_expr(const BDDt &r) const;
};

#endif
