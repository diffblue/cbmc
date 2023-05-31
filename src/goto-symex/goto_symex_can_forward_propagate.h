/*******************************************************************\

Module: Symbolic Execution Constant Propagation

Author: Michael Tautschig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// GOTO Symex constant propagation

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_CAN_FORWARD_PROPAGATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_CAN_FORWARD_PROPAGATE_H

#include <util/expr.h>
#include <util/expr_util.h>

class goto_symex_can_forward_propagatet : public can_forward_propagatet
{
public:
  explicit goto_symex_can_forward_propagatet(const namespacet &ns)
    : can_forward_propagatet(ns)
  {
  }

protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_mult)
    {
      bool found_non_constant = false;

      // propagate stuff with sizeof in it
      for(const auto &op : expr.operands())
      {
        if(op.find(ID_C_c_sizeof_type).is_not_nil())
          return true;
        else if(!is_constant(op))
          found_non_constant = true;
      }

      return !found_non_constant;
    }
    else if(expr.id() == ID_with)
    {
      // this is bad
#if 0
      for(const auto &op : expr.operands())
      {
        if(!is_constant(op))
          return false;
      }

      return true;
#else
      return false;
#endif
    }

    return can_forward_propagatet::is_constant(expr);
  }
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_CAN_FORWARD_PROPAGATE_H
