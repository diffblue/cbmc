/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "base_type.h"
#include "byte_operators.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_expr.h"

bool simplify_exprt::simplify_member(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  const irep_idt &component_name=
    to_member_expr(expr).get_component_name();

  exprt &op=expr.op0();
  const typet &op_type=ns.follow(op.type());

  if(op.id()==ID_with)
  {
    // the following optimization only works on structs,
    // and not on unions

    if(op.operands().size()>=3 &&
       op_type.id()==ID_struct)
    {
      exprt::operandst &operands=op.operands();

      while(operands.size()>1)
      {
        exprt &op1=operands[operands.size()-2];
        exprt &op2=operands[operands.size()-1];

        if(op1.get(ID_component_name)==component_name)
        {
          // found it!
          exprt tmp;
          tmp.swap(op2);
          expr.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
        else // something else, get rid of it
          operands.resize(operands.size()-2);
      }

      if(op.operands().size()==1)
      {
        exprt tmp;
        tmp.swap(op.op0());
        op.swap(tmp);
        // do this recursively
        simplify_member(expr);
      }

      return false;
    }
    else if(op_type.id()==ID_union)
    {
      const with_exprt &with_expr=to_with_expr(op);

      if(with_expr.where().get(ID_component_name)==component_name)
      {
        // WITH(s, .m, v).m -> v
        expr=with_expr.new_value();

        // do this recursively
        simplify_rec(expr);

        return false;
      }
    }
  }
  else if(op.id()==ID_update)
  {
    if(op.operands().size()==3 &&
       op_type.id()==ID_struct)
    {
      const update_exprt &update_expr=to_update_expr(op);
      const exprt::operandst &designator=update_expr.designator();

      // look at very first designator
      if(designator.size()==1 &&
         designator.front().id()==ID_member_designator)
      {
        if(designator.front().get(ID_component_name)==component_name)
        {
          // UPDATE(s, .m, v).m -> v
          exprt tmp=update_expr.new_value();
          expr.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
        // the following optimization only works on structs,
        // and not on unions
        else if(op_type.id()==ID_struct)
        {
          // UPDATE(s, .m1, v).m2 -> s.m2
          exprt tmp=update_expr.old();
          op.swap(tmp);

          // do this recursively
          simplify_rec(expr);

          return false;
        }
      }
    }
  }
  else if(op.id()==ID_struct ||
          op.id()==ID_constant)
  {
    if(op_type.id()==ID_struct)
    {
      // pull out the right member
      const struct_typet &struct_type=to_struct_type(op_type);
      if(struct_type.has_component(component_name))
      {
        std::size_t number=struct_type.component_number(component_name);
        exprt tmp;
        tmp.swap(op.operands()[number]);
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(op.id()==ID_byte_extract_little_endian ||
          op.id()==ID_byte_extract_big_endian)
  {
    if(op_type.id()==ID_struct)
    {
      // This rewrites byte_extract(s, o, struct_type).member
      // to byte_extract(s, o+member_offset, member_type)

      const struct_typet &struct_type=to_struct_type(op_type);
      const struct_typet::componentt &component=
        struct_type.get_component(component_name);

      if(component.is_nil() || component.type().id()==ID_c_bit_field)
        return true;

      // add member offset to index
      mp_integer offset_int=member_offset(struct_type, component_name, ns);
      if(offset_int==-1)
        return true;

      const exprt &struct_offset=op.op1();
      exprt member_offset=from_integer(offset_int, struct_offset.type());
      plus_exprt final_offset(struct_offset, member_offset);
      simplify_node(final_offset);

      byte_extract_exprt result(op.id(), op.op0(), final_offset, expr.type());
      expr.swap(result);

      simplify_rec(expr);

      return false;
    }
    else if(op_type.id() == ID_union)
    {
      // rewrite byte_extract(X, 0).member to X
      // if the type of X is that of the member
      const auto &byte_extract_expr = to_byte_extract_expr(op);
      if(byte_extract_expr.offset().is_zero())
      {
        const union_typet &union_type = to_union_type(op_type);
        const typet &subtype = union_type.component_type(component_name);

        if(subtype == byte_extract_expr.op().type())
        {
          exprt tmp = byte_extract_expr.op();
          expr.swap(tmp);

          return false;
        }
      }
    }
  }
  else if(op.id()==ID_union && op_type.id()==ID_union)
  {
    // trivial?
    if(ns.follow(to_union_expr(op).op().type())==ns.follow(expr.type()))
    {
      exprt tmp=to_union_expr(op).op();
      expr.swap(tmp);
      return false;
    }

    // need to convert!
    mp_integer target_size=
      pointer_offset_size(expr.type(), ns);

    if(target_size!=-1)
    {
      mp_integer target_bits=target_size*8;
      const auto bits=expr2bits(op, true);

      if(bits.has_value() &&
         mp_integer(bits->size())>=target_bits)
      {
        std::string bits_cut=std::string(*bits, 0, integer2size_t(target_bits));

        exprt tmp=bits2expr(bits_cut, expr.type(), true);

        if(tmp.is_not_nil())
        {
          expr=tmp;
          return false;
        }
      }
    }
  }
  else if(op.id() == ID_typecast)
  {
    // Try to look through member(cast(x)) if the cast is between structurally
    // identical types:
    if(base_type_eq(op_type, op.op0().type(), ns))
    {
      expr.op0() = op.op0();
      simplify_member(expr);
      return false;
    }
  }
  else if(op.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(op);
    exprt cond=if_expr.cond();

    member_exprt member_false=to_member_expr(expr);
    member_false.compound()=if_expr.false_case();

    to_member_expr(expr).compound()=if_expr.true_case();

    expr=if_exprt(cond, expr, member_false, expr.type());
    simplify_rec(expr);

    return false;
  }

  return true;
}
