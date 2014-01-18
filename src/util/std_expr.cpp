/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <cassert>

#include "arith_tools.h"
#include "byte_operators.h"
#include "config.h"
#include "namespace.h"
#include "pointer_offset_size.h"

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

/*******************************************************************\

Function: build_object_descriptor_rec

  Inputs:

 Outputs:

 Purpose: Build an object_descriptor_exprt from a given expr

\*******************************************************************/

static void build_object_descriptor_rec(
  const namespacet &ns,
  const exprt &expr,
  object_descriptor_exprt &dest)
{
  const signedbv_typet index_type(config.ansi_c.pointer_width);

  if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_object_descriptor_rec(ns, index.array(), dest);

    mp_integer sub_size=pointer_offset_size(ns, expr.type());
    assert(sub_size>0);

    dest.offset()=
      plus_exprt(dest.offset(),
                 mult_exprt(typecast_exprt(index.index(), index_type),
                            from_integer(sub_size, index_type)));
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);
    const exprt &struct_op=member.struct_op();
    const typet &struct_type=ns.follow(struct_op.type());

    build_object_descriptor_rec(ns, struct_op, dest);

    if(struct_type.id()==ID_union)
      return;

    mp_integer offset=
      member_offset(ns,
                    to_struct_type(struct_type),
                    member.get_component_name());
    assert(offset>=0);

    dest.offset()=
      plus_exprt(dest.offset(), from_integer(offset, index_type));
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &be=to_byte_extract_expr(expr);

    dest.object()=be.op();

    build_object_descriptor_rec(ns, be.op(), dest);

    dest.offset()=
      plus_exprt(dest.offset(),
                 typecast_exprt(to_byte_extract_expr(expr).offset(),
                                index_type));
  }
}

/*******************************************************************\

Function: object_descriptor_exprt::build

  Inputs:

 Outputs:

 Purpose: Build an object_descriptor_exprt from a given expr

\*******************************************************************/

void object_descriptor_exprt::build(
  const exprt &expr,
  const namespacet &ns)
{
  assert(object().id()==ID_unknown);
  object()=expr;

  if(offset().id()==ID_unknown)
    offset()=from_integer(0, signedbv_typet(config.ansi_c.pointer_width));

  build_object_descriptor_rec(ns, expr, *this);

  assert(root_object().type().id()!=ID_empty);
}

