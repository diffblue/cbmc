/*******************************************************************\

Module: Symbolic Execution Constant Propagation

Author: Michael Tautschig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// GOTO Symex constant propagation

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H

#include <util/expr_util.h>
#include <util/std_expr.h>

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
    else if(auto if_expr = expr_try_dynamic_cast<if_exprt>(expr))
    {
      // consider ?: constant if both branches are constants, irrespective of
      // the condition
      return is_constant(if_expr->true_case()) &&
             is_constant(if_expr->false_case());
    }

    return is_constantt::is_constant(expr);
  }
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H
