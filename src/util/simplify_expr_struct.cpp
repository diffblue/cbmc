/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "byte_operators.h"
#include "invariant.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "std_expr.h"

simplify_exprt::resultt<>
simplify_exprt::simplify_member(const member_exprt &expr)
{
  const irep_idt &component_name=
    to_member_expr(expr).get_component_name();

  const exprt &op = expr.compound();
  const typet &op_type=ns.follow(op.type());

  if(op.id()==ID_with)
  {
    // the following optimization only works on structs,
    // and not on unions

    if(op.operands().size()>=3 &&
       op_type.id()==ID_struct)
    {
      exprt::operandst new_operands = op.operands();

      while(new_operands.size() > 1)
      {
        exprt &op1 = new_operands[new_operands.size() - 2];
        exprt &op2 = new_operands[new_operands.size() - 1];

        if(op1.get(ID_component_name)==component_name)
        {
          // found it!
          DATA_INVARIANT(
            op2.type() == expr.type(),
            "member expression type must match component type");
          exprt tmp;
          tmp.swap(op2);

          // do this recursively
          return changed(simplify_rec(tmp));
        }
        else // something else, get rid of it
          new_operands.resize(new_operands.size() - 2);
      }

      DATA_INVARIANT(new_operands.size() == 1, "post-condition of loop");

      auto new_member_expr = expr;
      new_member_expr.struct_op() = new_operands.front();
      // do this recursively
      return changed(simplify_member(new_member_expr));
    }
    else if(op_type.id()==ID_union)
    {
      const with_exprt &with_expr=to_with_expr(op);

      if(with_expr.where().get(ID_component_name)==component_name)
      {
        // WITH(s, .m, v).m -> v
        auto tmp = with_expr.new_value();

        // do this recursively
        return changed(simplify_rec(tmp));
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

          // do this recursively
          return changed(simplify_rec(tmp));
        }
        // the following optimization only works on structs,
        // and not on unions
        else if(op_type.id()==ID_struct)
        {
          // UPDATE(s, .m1, v).m2 -> s.m2
          auto new_expr = expr;
          new_expr.struct_op() = update_expr.old();

          // do this recursively
          return changed(simplify_rec(new_expr));
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
        DATA_INVARIANT(
          op.operands()[number].type() == expr.type(),
          "member expression type must match component type");
        return op.operands()[number];
      }
    }
  }
  else if(op.id()==ID_byte_extract_little_endian ||
          op.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr = to_byte_extract_expr(op);

    if(op_type.id()==ID_struct)
    {
      // This rewrites byte_extract(s, o, struct_type).member
      // to byte_extract(s, o+member_offset, member_type)

      const struct_typet &struct_type=to_struct_type(op_type);
      const struct_typet::componentt &component=
        struct_type.get_component(component_name);

      if(
        component.is_nil() || component.type().id() == ID_c_bit_field ||
        component.type().id() == ID_bool)
      {
        return unchanged(expr);
      }

      // add member offset to index
      auto offset_int = member_offset(struct_type, component_name, ns);
      if(!offset_int.has_value())
        return unchanged(expr);

      const exprt &struct_offset = byte_extract_expr.offset();
      exprt member_offset = from_integer(*offset_int, struct_offset.type());
      exprt final_offset =
        simplify_node(plus_exprt(struct_offset, member_offset));

      byte_extract_exprt result(
        op.id(), byte_extract_expr.op(), final_offset, expr.type());

      return changed(simplify_rec(result)); // recursive call
    }
    else if(op_type.id() == ID_union)
    {
      // rewrite byte_extract(X, 0).member to X
      // if the type of X is that of the member
      if(byte_extract_expr.offset().is_zero())
      {
        const union_typet &union_type = to_union_type(op_type);
        const typet &subtype = union_type.component_type(component_name);

        if(subtype == byte_extract_expr.op().type())
          return byte_extract_expr.op();
      }
    }
  }
  else if(op.id()==ID_union && op_type.id()==ID_union)
  {
    // trivial?
    if(to_union_expr(op).op().type() == expr.type())
      return to_union_expr(op).op();

    // need to convert!
    auto target_size = pointer_offset_size(expr.type(), ns);

    if(target_size.has_value())
    {
      mp_integer target_bits = target_size.value() * 8;
      const auto bits=expr2bits(op, true);

      if(bits.has_value() &&
         mp_integer(bits->size())>=target_bits)
      {
        std::string bits_cut =
          std::string(*bits, 0, numeric_cast_v<std::size_t>(target_bits));

        auto tmp = bits2expr(bits_cut, expr.type(), true);

        if(tmp.has_value())
          return std::move(*tmp);
      }
    }
  }
  else if(op.id() == ID_typecast)
  {
    const auto &typecast_expr = to_typecast_expr(op);

    // Try to look through member(cast(x)) if the cast is between structurally
    // identical types:
    if(op_type == typecast_expr.op().type())
    {
      auto new_expr = expr;
      new_expr.struct_op() = typecast_expr.op();
      return changed(simplify_member(new_expr));
    }

    // Try to translate into an equivalent member (perhaps nested) of the type
    // being cast (for example, this might turn ((struct A)x).field1 into
    // x.substruct.othersubstruct.field2, if field1 and field2 have the same
    // type and offset with respect to x.
    if(op_type.id() == ID_struct)
    {
      optionalt<mp_integer> requested_offset =
        member_offset(to_struct_type(op_type), component_name, ns);
      if(requested_offset.has_value())
      {
        auto equivalent_member = get_subexpression_at_offset(
          typecast_expr.op(), *requested_offset, expr.type(), ns);

        // Guess: turning this into a byte-extract operation is not really an
        // optimisation.
        if(
          equivalent_member.has_value() &&
          equivalent_member.value().id() != ID_byte_extract_little_endian &&
          equivalent_member.value().id() != ID_byte_extract_big_endian)
        {
          auto tmp = equivalent_member.value();
          return changed(simplify_rec(tmp));
        }
      }
    }
  }
  else if(op.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(op);
    exprt cond=if_expr.cond();

    member_exprt member_false=to_member_expr(expr);
    member_false.compound()=if_expr.false_case();

    member_exprt member_true = to_member_expr(expr);
    member_true.compound() = if_expr.true_case();

    auto tmp = if_exprt(cond, member_true, member_false, expr.type());
    return changed(simplify_rec(tmp));
  }
  else if(op.id() == ID_let)
  {
    // Push a member operator inside a let binding, to avoid the let bisecting
    // structures we otherwise know how to analyse, such as
    // (let x = 1 in ({x, x})).field1 --> let x = 1 in ({x, x}.field1) -->
    // let x = 1 in x
    member_exprt pushed_in_member = to_member_expr(expr);
    pushed_in_member.op() = to_let_expr(op).where();
    auto new_expr = op;
    to_let_expr(new_expr).where() = pushed_in_member;
    to_let_expr(new_expr).type() = to_let_expr(new_expr).where().type();

    return changed(simplify_rec(new_expr));
  }

  return unchanged(expr);
}
