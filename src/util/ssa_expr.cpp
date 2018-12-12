/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_expr.h"

#include <sstream>
#include <cassert>

#include <util/arith_tools.h>

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

    const mp_integer idx = numeric_cast_v<mp_integer>(index.index());
    os << '[' << idx << ']';
  }
  else if(expr.id()==ID_symbol)
  {
    auto symid=to_symbol_expr(expr).get_identifier();
    os << symid;
    l1_object_os << symid;

    if(!l0.empty())
    {
      // Distinguish different threads of execution
      os << '!' << l0;
      l1_object_os << '!' << l0;
    }

    if(!l1.empty())
    {
      // Distinguish different calls to the same function (~stack frame)
      os << '@' << l1;
      l1_object_os << '@' << l1;
    }

    if(!l2.empty())
    {
      // Distinguish SSA steps for the same variable
      os << '#' << l2;
    }
  }
  else
    UNREACHABLE;
}

/* Used to determine whether or not an identifier can be built
   * before trying and getting an exception */
bool ssa_exprt::can_build_identifier(const exprt &expr)
{
  if(expr.id()==ID_symbol)
    return true;
  else if(expr.id() == ID_member)
    return can_build_identifier(to_member_expr(expr).compound());
  else if(expr.id() == ID_index)
    return can_build_identifier(to_index_expr(expr).array());
  else
    return false;
}

static std::pair<irep_idt, irep_idt> build_identifier(
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

void ssa_exprt::update_identifier()
{
  const irep_idt &l0 = get_level_0();
  const irep_idt &l1 = get_level_1();
  const irep_idt &l2 = get_level_2();

  auto idpair = build_identifier(get_original_expr(), l0, l1, l2);
  set_identifier(idpair.first);
  set(ID_L1_object_identifier, idpair.second);
}
