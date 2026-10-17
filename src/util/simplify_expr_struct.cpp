/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "byte_operators.h"
#include "c_types.h"
#include "config.h"
#include "expr_util.h"
#include "invariant.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "simplify_utils.h"
#include "std_expr.h"

/// The component of the struct value \p src (looking into struct members,
/// union values, little-endian byte extracts at a constant offset and byte
/// updates of other bytes) that occupies exactly \p width bits from bit
/// \p offset_bits.
static std::optional<exprt> struct_component_at_bits(
  const exprt &src,
  const mp_integer &offset_bits,
  const mp_integer &width,
  const namespacet &ns)
{
  if(src.id() == ID_byte_extract_little_endian)
  {
    const auto &be = to_byte_extract_expr(src);
    const auto offset = numeric_cast<mp_integer>(be.offset());
    if(!offset.has_value())
      return {};
    return struct_component_at_bits(
      be.op(), *offset * be.get_bits_per_byte() + offset_bits, width, ns);
  }
  if(src.id() == ID_union)
    return struct_component_at_bits(
      to_union_expr(src).op(), offset_bits, width, ns);
  // a byte update that does not touch these bits
  if(src.id() == ID_byte_update_little_endian)
  {
    const auto &bu = to_byte_update_expr(src);
    const auto offset = numeric_cast<mp_integer>(bu.offset());
    const auto update_bits = pointer_offset_bits(bu.value().type(), ns);
    if(!offset.has_value() || !update_bits.has_value())
      return {};
    const mp_integer first = *offset * bu.get_bits_per_byte();
    if(offset_bits + width <= first || first + *update_bits <= offset_bits)
    {
      return struct_component_at_bits(bu.op(), offset_bits, width, ns);
    }
    return {};
  }
  if(src.id() != ID_struct)
    return {};
  const struct_typet &struct_type =
    src.type().id() == ID_struct_tag
      ? ns.follow_tag(to_struct_tag_type(src.type()))
      : to_struct_type(src.type());
  const auto &components = struct_type.components();
  if(components.size() != src.operands().size())
    return {};
  for(std::size_t i = 0; i < components.size(); ++i)
  {
    const auto c_offset =
      member_offset_bits(struct_type, components[i].get_name(), ns);
    const auto c_width = pointer_offset_bits(components[i].type(), ns);
    if(!c_offset.has_value() || !c_width.has_value())
      return {};
    if(*c_offset == offset_bits && *c_width == width)
      return src.operands()[i];
    if(*c_offset <= offset_bits && offset_bits + width <= *c_offset + *c_width)
    {
      return struct_component_at_bits(
        src.operands()[i], offset_bits - *c_offset, width, ns);
    }
  }
  return {};
}

simplify_exprt::resultt<>
simplify_exprt::simplify_member(const member_exprt &expr)
{
  const irep_idt &component_name=
    to_member_expr(expr).get_component_name();

  const exprt &op = expr.compound();

  if(op.id()==ID_with)
  {
    // the following optimization only works on structs,
    // and not on unions

    if(
      op.operands().size() >= 3 &&
      (op.type().id() == ID_struct || op.type().id() == ID_struct_tag))
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

          return op2;
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
    else if(op.type().id() == ID_union || op.type().id() == ID_union_tag)
    {
      const with_exprt &with_expr=to_with_expr(op);

      if(with_expr.where().get(ID_component_name)==component_name)
      {
        // WITH(s, .m, v).m -> v
        return with_expr.new_value();
      }
    }
  }
  else if(op.id()==ID_update)
  {
    if(
      op.operands().size() == 3 &&
      (op.type().id() == ID_struct || op.type().id() == ID_struct_tag))
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
          return update_expr.new_value();
        }
        // the following optimization only works on structs,
        // and not on unions
        else if(op.type().id() == ID_struct || op.type().id() == ID_struct_tag)
        {
          // UPDATE(s, .m1, v).m2 -> s.m2
          auto new_expr = expr;
          new_expr.struct_op() = update_expr.old();

          // do this recursively
          return changed(simplify_member(new_expr));
        }
      }
    }
  }
  else if(op.id() == ID_compound_literal)
  {
    // Look through compound_literal to the underlying struct
    auto new_expr = expr;
    new_expr.struct_op() = to_unary_expr(op).op();
    return changed(simplify_member(new_expr));
  }
  else if(op.id() == ID_struct)
  {
    // pull out the right member
    const struct_typet &struct_type =
      op.type().id() == ID_struct_tag
        ? ns.follow_tag(to_struct_tag_type(op.type()))
        : to_struct_type(op.type());
    if(struct_type.has_component(component_name))
    {
      std::size_t number = struct_type.data_component_number(component_name);
      DATA_INVARIANT(
        op.operands().size() > number,
        "struct expression must have sufficiently many operands");
      DATA_INVARIANT(
        op.operands()[number].type() == expr.type(),
        "member expression type must match component type");
      return op.operands()[number];
    }
  }
  else if(op.id()==ID_byte_extract_little_endian ||
          op.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr = to_byte_extract_expr(op);

    if(op.type().id() == ID_struct || op.type().id() == ID_struct_tag)
    {
      // This rewrites byte_extract(s, o, struct_type).member
      // to byte_extract(s, o+member_offset, member_type)

      const struct_typet &struct_type =
        op.type().id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(op.type()))
          : to_struct_type(op.type());
      const struct_typet::componentt &component=
        struct_type.get_component(component_name);

      if(component.is_nil())
        return unchanged(expr);

      // N5008 [basic.memobj] / CBMC byte semantics: a byte update that does
      // not overlap this member's bits does not change it.  Drop such
      // updates of the extracted object (the member can then be read from
      // the object as it was, e.g. a field-sensitive symbol whose value is
      // known).
      if(
        op.id() == ID_byte_extract_little_endian &&
        byte_extract_expr.op().id() == ID_byte_update_little_endian)
      {
        const auto member_bits =
          member_offset_bits(struct_type, component_name, ns);
        const auto member_width = pointer_offset_bits(component.type(), ns);
        const auto extract_offset =
          numeric_cast<mp_integer>(byte_extract_expr.offset());
        if(
          member_bits.has_value() && member_width.has_value() &&
          extract_offset.has_value())
        {
          const std::size_t bits_per_byte =
            byte_extract_expr.get_bits_per_byte();
          const mp_integer lo = *extract_offset * bits_per_byte + *member_bits;
          const mp_integer hi = lo + *member_width;
          const exprt *source = &byte_extract_expr.op();
          while(source->id() == ID_byte_update_little_endian)
          {
            const auto &bu = to_byte_update_expr(*source);
            const auto offset = numeric_cast<mp_integer>(bu.offset());
            const auto update_bits = pointer_offset_bits(bu.value().type(), ns);
            if(!offset.has_value() || !update_bits.has_value())
              break;
            const mp_integer first = *offset * bu.get_bits_per_byte();
            if(!(hi <= first || first + *update_bits <= lo))
              break;
            source = &bu.op();
          }
          if(source != &byte_extract_expr.op())
          {
            byte_extract_exprt new_extract = byte_extract_expr;
            new_extract.op() = *source;
            member_exprt new_member = expr;
            new_member.struct_op() = new_extract;
            return changed(simplify_member(new_member));
          }
        }
      }

      // A bit field (or a single-bit Boolean member) need not start at a
      // byte boundary: extract the bytes that hold it and select its bits.
      // Little-endian only, where bit k of the extracted bytes is bit
      // (byte offset * 8 + k) of the object.  Without this, a bit field read
      // back through a byte_extract stayed symbolic, and so did everything
      // depending on it (libc++'s alternate string layout keeps the short
      // size in a 7-bit field: every string comparison was an unbounded
      // memcmp).
      if(component.type().id() == ID_c_bit_field || component.is_boolean())
      {
        if(op.id() != ID_byte_extract_little_endian)
          return unchanged(expr);
        const auto offset_bits =
          member_offset_bits(struct_type, component_name, ns);
        const auto width = pointer_offset_bits(component.type(), ns);
        const std::size_t bits_per_byte = byte_extract_expr.get_bits_per_byte();
        if(!offset_bits.has_value() || !width.has_value() || *width == 0)
          return unchanged(expr);
        const mp_integer first_byte = *offset_bits / bits_per_byte;
        const mp_integer shift = *offset_bits % bits_per_byte;
        const mp_integer bytes =
          (shift + *width + bits_per_byte - 1) / bits_per_byte;
        const exprt &struct_offset = byte_extract_expr.offset();
        // The source is a struct value with a component at exactly these
        // bits (the field-sensitive view of the same struct, or of a union
        // member of the same layout): that component.
        const auto source_offset =
          numeric_cast<mp_integer>(simplify_rec(struct_offset).expr);
        if(source_offset.has_value())
        {
          const auto found = struct_component_at_bits(
            byte_extract_expr.op(),
            *source_offset * bits_per_byte + *offset_bits,
            *width,
            ns);
          if(found.has_value() && found->type() == expr.type())
            return *found;
        }
        exprt final_offset = simplify_plus(plus_exprt(
          struct_offset, from_integer(first_byte, struct_offset.type())));
        byte_extract_exprt containing(
          op.id(),
          byte_extract_expr.op(),
          final_offset,
          bits_per_byte,
          unsignedbv_typet{numeric_cast_v<std::size_t>(bytes * bits_per_byte)});
        exprt value = simplify_byte_extract(containing);
        exprt bits = simplify_extractbits(extractbits_exprt{
          value,
          from_integer(shift, c_index_type()),
          unsignedbv_typet{numeric_cast_v<std::size_t>(*width)}});
        exprt result =
          simplify_typecast(typecast_exprt{std::move(bits), expr.type()});
        // only a constant: the member may be an assignment's target, and
        // extractbits is no lvalue
        if(!result.is_constant())
          return unchanged(expr);
        return std::move(result);
      }

      // add member offset to index
      auto offset_int = member_offset(struct_type, component_name, ns);
      if(!offset_int.has_value())
        return unchanged(expr);

      const exprt &struct_offset = byte_extract_expr.offset();
      exprt member_offset = from_integer(*offset_int, struct_offset.type());
      exprt final_offset =
        simplify_plus(plus_exprt(struct_offset, member_offset));

      byte_extract_exprt result(
        op.id(),
        byte_extract_expr.op(),
        final_offset,
        byte_extract_expr.get_bits_per_byte(),
        expr.type());

      return changed(simplify_byte_extract(result)); // recursive call
    }
    else if(op.type().id() == ID_union || op.type().id() == ID_union_tag)
    {
      // rewrite byte_extract(X, 0).member to X
      // if the type of X is that of the member
      if(byte_extract_expr.offset() == 0)
      {
        const union_typet &union_type =
          op.type().id() == ID_union_tag
            ? ns.follow_tag(to_union_tag_type(op.type()))
            : to_union_type(op.type());
        const typet &subtype = union_type.component_type(component_name);

        if(subtype == byte_extract_expr.op().type())
          return byte_extract_expr.op();
      }
    }
  }
  else if(
    op.id() == ID_union &&
    (op.type().id() == ID_union || op.type().id() == ID_union_tag))
  {
    // trivial?
    if(to_union_expr(op).op().type() == expr.type())
      return to_union_expr(op).op();

    // need to convert!
    auto target_size = pointer_offset_size(expr.type(), ns);

    if(target_size.has_value())
    {
      mp_integer target_bits = target_size.value() * config.ansi_c.char_width;
      const auto bits = expr2bits(op, true, ns);

      if(bits.has_value() &&
         mp_integer(bits->size())>=target_bits)
      {
        std::string bits_cut =
          std::string(*bits, 0, numeric_cast_v<std::size_t>(target_bits));

        auto tmp = bits2expr(bits_cut, expr.type(), true, ns);

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
    if(op.type() == typecast_expr.op().type())
    {
      auto new_expr = expr;
      new_expr.struct_op() = typecast_expr.op();
      return changed(simplify_member(new_expr));
    }

    // Try to translate into an equivalent member (perhaps nested) of the type
    // being cast (for example, this might turn ((struct A)x).field1 into
    // x.substruct.othersubstruct.field2, if field1 and field2 have the same
    // type and offset with respect to x.
    if(op.type().id() == ID_struct || op.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        op.type().id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(op.type()))
          : to_struct_type(op.type());
      std::optional<mp_integer> requested_offset =
        member_offset(struct_type, component_name, ns);
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

simplify_exprt::resultt<>
simplify_exprt::simplify_member_preorder(const member_exprt &expr)
{
  const exprt &compound = expr.compound();

  if(compound.id() == ID_if)
  {
    if_exprt if_expr = lift_if(expr, 0);
    return changed(simplify_if_preorder(if_expr));
  }
  else
  {
    auto r_it = simplify_rec(compound); // recursive call
    if(r_it.has_changed())
    {
      auto tmp = expr;
      tmp.compound() = r_it.expr;
      return tmp;
    }
  }

  return unchanged(expr);
}
