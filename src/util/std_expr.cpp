/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include "arith_tools.h"

#include "std_expr.h"

/*******************************************************************\

Function: constant_exprt::value_is_zero_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool constant_exprt::value_is_zero_string() const
{
  const std::string val=id2string(get_value());
  return val.find_first_not_of('0')==std::string::npos;
}

/*******************************************************************\

Function: disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt disjunction(const exprt::operandst &op)
{
  if(op.empty())
    return false_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    or_exprt result;
    result.operands()=op;
    return result;
  }
}

/*******************************************************************\

Function: conjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt conjunction(const exprt::operandst &op)
{
  if(op.empty())
    return true_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    and_exprt result;
    result.operands()=op;
    return result;
  }
}

/*******************************************************************\

Function: build_identifier_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void build_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  std::ostringstream &oss)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);

    build_identifier_rec(member.struct_op(), l0, l1, oss);

    oss << '.' << member.get_component_name();
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_identifier_rec(index.array(), l0, l1, oss);

    mp_integer idx;
    if(to_integer(to_constant_expr(index.index()), idx))
      assert(false);

    oss << '[' << idx << ']';
  }
  else if(expr.id()==ID_symbol)
  {
    oss << to_symbol_expr(expr).get_identifier();

    if(!l0.empty())
      oss << '!' << l0;

    if(!l1.empty())
      oss << '@' << l1;
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

  build_identifier_rec(get_original_expr(), l0, l1, oss);

  if(!l2.empty())
    oss << '#' << l2;

  set_identifier(oss.str());
}

