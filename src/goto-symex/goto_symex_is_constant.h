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

#include "goto_symex_state.h"

class goto_symex_is_constantt : public is_constantt
{
protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_mult)
    {
      // propagate stuff with sizeof in it
      forall_operands(it, expr)
      {
        if(it->find(ID_C_c_sizeof_type).is_not_nil())
          return true;
        else if(!is_constant(*it))
          return false;
      }

      return true;
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
    else if(expr.id() == ID_symbol)
    {
      // we only ever assign to a single guard once, we can treat it as constant
      return to_ssa_expr(expr).get_object_name() ==
             goto_symex_statet::guard_identifier();
    }

    return is_constantt::is_constant(expr);
  }
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_IS_CONSTANT_H
