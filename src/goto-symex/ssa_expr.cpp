/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/arith_tools.h>

#include "ssa_expr.h"

/*******************************************************************\

Function: build_identifier_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void build_ssa_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  std::ostream &os)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);

    build_ssa_identifier_rec(member.struct_op(), l0, l1, os);

    os << '.' << member.get_component_name();
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_ssa_identifier_rec(index.array(), l0, l1, os);

    mp_integer idx;
    if(to_integer(to_constant_expr(index.index()), idx))
      assert(false);

    os << '[' << idx << ']';
  }
  else if(expr.id()==ID_symbol)
  {
    os << to_symbol_expr(expr).get_identifier();

    if(!l0.empty())
      os << '!' << l0;

    if(!l1.empty())
      os << '@' << l1;
  }
  else
    assert(false);
}

/*******************************************************************\

Function: ssa_exprt::update_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_exprt::update_identifier()
{
  std::ostringstream oss;

  const irep_idt &l0=get_level_0();
  const irep_idt &l1=get_level_1();
  const irep_idt &l2=get_level_2();

  build_ssa_identifier_rec(get_original_expr(), l0, l1, oss);

  if(!l2.empty())
    oss << '#' << l2;

  set_identifier(oss.str());
}
