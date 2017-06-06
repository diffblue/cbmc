/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <sstream>
#include <cassert>

#include <util/arith_tools.h>

#include "ssa_expr.h"

static void build_ssa_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2,
  std::ostream &os,
  std::ostream &l1_object_os)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);

    build_ssa_identifier_rec(member.struct_op(), l0, l1, l2, os, l1_object_os);

    os << '.' << member.get_component_name();
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_ssa_identifier_rec(index.array(), l0, l1, l2, os, l1_object_os);

    mp_integer idx;
    if(to_integer(to_constant_expr(index.index()), idx))
      assert(false);

    os << '[' << idx << ']';
  }
  else if(expr.id()==ID_symbol)
  {
    auto symid=to_symbol_expr(expr).get_identifier();
    os << symid;
    l1_object_os << symid;

    if(!l0.empty())
    {
      os << '!' << l0;
      l1_object_os << '!' << l0;
    }

    if(!l1.empty())
    {
      os << '@' << l1;
      l1_object_os << '@' << l1;
    }

    if(!l2.empty())
      os << '#' << l2;
  }
  else
    assert(false);
}

std::pair<irep_idt, irep_idt> ssa_exprt::build_identifier(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2)
{
  std::ostringstream oss;
  std::ostringstream l1_object_oss;

  build_ssa_identifier_rec(expr, l0, l1, l2, oss, l1_object_oss);

  return std::make_pair(irep_idt(oss.str()), irep_idt(l1_object_oss.str()));
}
