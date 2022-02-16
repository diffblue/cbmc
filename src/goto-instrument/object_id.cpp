/*******************************************************************\

Module: Object Identifiers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Object Identifiers

#include "object_id.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/pointer_expr.h>

enum class get_modet { LHS_R, LHS_W, READ };

void get_objects_rec(
  get_modet mode,
  const exprt &expr,
  object_id_sett &dest,
  const std::string &suffix)
{
  if(expr.id()==ID_symbol)
  {
    if(mode==get_modet::LHS_W || mode==get_modet::READ)
      dest.insert(object_idt(to_symbol_expr(expr)));
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    if(mode==get_modet::LHS_R || mode==get_modet::READ)
      get_objects_rec(get_modet::READ, index_expr.index(), dest, "");

    if(mode==get_modet::LHS_R)
      get_objects_rec(get_modet::READ, index_expr.array(), dest, "[]"+suffix);
    else
      get_objects_rec(mode, index_expr.array(), dest, "[]"+suffix);
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    if(mode==get_modet::LHS_R || mode==get_modet::READ)
      get_objects_rec(get_modet::READ, if_expr.cond(), dest, "");

    get_objects_rec(mode, if_expr.true_case(), dest, suffix);
    get_objects_rec(mode, if_expr.false_case(), dest, suffix);
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);

    get_objects_rec(mode, member_expr.struct_op(), dest,
      "."+id2string(member_expr.get_component_name())+suffix);
  }
  else if(expr.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=
      to_dereference_expr(expr);

    if(mode==get_modet::LHS_R || mode==get_modet::READ)
      get_objects_rec(get_modet::READ, dereference_expr.pointer(), dest, "");
  }
  else
  {
    if(mode==get_modet::LHS_R || mode==get_modet::READ)
      forall_operands(it, expr)
        get_objects_rec(get_modet::READ, *it, dest, "");
  }
}

void get_objects(const exprt &expr, object_id_sett &dest)
{
  get_objects_rec(get_modet::READ, expr, dest, "");
}

void get_objects_r(const code_assignt &assign, object_id_sett &dest)
{
  get_objects_rec(get_modet::LHS_R, assign.lhs(), dest, "");
  get_objects_rec(get_modet::READ, assign.rhs(), dest, "");
}

void get_objects_w(const code_assignt &assign, object_id_sett &dest)
{
  get_objects_rec(get_modet::LHS_W, assign.lhs(), dest, "");
}

void get_objects_w(const exprt &lhs, object_id_sett &dest)
{
  get_objects_rec(get_modet::LHS_W, lhs, dest, "");
}

void get_objects_r_lhs(const exprt &lhs, object_id_sett &dest)
{
  get_objects_rec(get_modet::LHS_R, lhs, dest, "");
}
