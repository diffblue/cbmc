/*******************************************************************\

Module: Symbolic Execution Constant Propagation

Author: Michael Tautschig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// GOTO Symex constant propagation

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H

#include <util/expr.h>
#include <util/expr_util.h>

class goto_symex_is_constantt : public is_constantt
{
protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_mult)
    {
      bool found_non_constant = false;

      // propagate stuff with sizeof in it
      forall_operands(it, expr)
      {
        if(it->find(ID_C_c_sizeof_type).is_not_nil())
          return true;
        else if(!is_constant(*it))
          found_non_constant = true;
      }

      return !found_non_constant;
    }
    else if(expr.id() == ID_with)
    {
      // this is bad
      /*
      forall_operands(it, expr)
      if(!is_constant(expr.op0()))
      return false;

      return true;
      */
      return false;
    }
    else if(expr.id() == ID_if)
    {
      // don't treat nested if_exprt as constant (even when they are!) as this
      // may give rise to large expressions that we repeatedly pass to the
      // simplifier; this is observable on regression/cbmc-library/memmove-01
      const if_exprt &if_expr = to_if_expr(expr);
      if(
        if_expr.true_case().id() == ID_if || if_expr.false_case().id() == ID_if)
      {
        return false;
      }
    }
    else if(expr.id() == ID_nondet_symbol)
      return true;

    return is_constantt::is_constant(expr);
  }
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H
