/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_pointers.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>

/// Map bytes according to the configured endianness. The key difference to
/// endianness_mapt is that bv_endianness_mapt is aware of the bit-level
/// encoding of types, which need not co-incide with the bit layout at
/// source-code level.
class bv_endianness_mapt : public endianness_mapt
{
public:
  bv_endianness_mapt(
    const typet &type,
    bool little_endian,
    const namespacet &_ns,
    const boolbv_widtht &_boolbv_width)
    : endianness_mapt(_ns), boolbv_width(_boolbv_width)
  {
    build(type, little_endian);
  }

protected:
  const boolbv_widtht &boolbv_width;

  void build_little_endian(const typet &type) override;
  void build_big_endian(const typet &type) override;
};

void bv_endianness_mapt::build_little_endian(const typet &src)
{
  const std::size_t width = boolbv_width(src);

  if(width == 0)
    return;

  const std::size_t new_size = map.size() + width;
  map.reserve(new_size);

  for(std::size_t i = map.size(); i < new_size; ++i)
    map.push_back(i);
}

void bv_endianness_mapt::build_big_endian(const typet &src)
{
  if(src.id() == ID_pointer)
    build_little_endian(src);
  else
    endianness_mapt::build_big_endian(src);
}

endianness_mapt
bv_pointerst::endianness_map(const typet &type, bool little_endian) const
{
  return bv_endianness_mapt{type, little_endian, ns, bv_width};
}

std::size_t bv_pointerst::get_object_width(const pointer_typet &) const
{
  // not actually type-dependent for now
  return config.bv_encoding.object_bits;
}

std::size_t bv_pointerst::get_offset_width(const pointer_typet &type) const
{
  const std::size_t pointer_width = type.get_width();
  const std::size_t object_width = get_object_width(type);
  PRECONDITION(pointer_width >= object_width);
  return pointer_width - object_width;
}

std::size_t bv_pointerst::get_address_width(const pointer_typet &type) const
{
  return type.get_width();
}

bvt bv_pointerst::object_literals(const bvt &bv, const pointer_typet &type)
  const
{
  const std::size_t offset_width = get_offset_width(type);
  const std::size_t object_width = get_object_width(type);
  PRECONDITION(bv.size() >= offset_width + object_width);

  return bvt(
    bv.begin() + offset_width, bv.begin() + offset_width + object_width);
}

bvt bv_pointerst::offset_literals(const bvt &bv, const pointer_typet &type)
  const
{
  const std::size_t offset_width = get_offset_width(type);
  PRECONDITION(bv.size() >= offset_width);

  return bvt(bv.begin(), bv.begin() + offset_width);
}

bvt bv_pointerst::object_offset_encoding(const bvt &object, const bvt &offset)
{
  bvt result;
  result.reserve(offset.size() + object.size());
  result.insert(result.end(), offset.begin(), offset.end());
  result.insert(result.end(), object.begin(), object.end());

  return result;
}

literalt bv_pointerst::convert_rest(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const exprt::operandst &operands=expr.operands();

  if(expr.id() == ID_is_invalid_pointer)
  {
    if(operands.size()==1 &&
       operands[0].type().id()==ID_pointer)
    {
      const bvt &bv=convert_bv(operands[0]);

      if(!bv.empty())
      {
        const pointer_typet &type = to_pointer_type(operands[0].type());
        bvt object_bv = object_literals(bv, type);

        bvt invalid_bv = object_literals(
          encode(pointer_logic.get_invalid_object(), type), type);

        const std::size_t object_bits = get_object_width(type);

        bvt equal_invalid_bv;
        equal_invalid_bv.reserve(object_bits);

        for(std::size_t i=0; i<object_bits; i++)
        {
          equal_invalid_bv.push_back(prop.lequal(object_bv[i], invalid_bv[i]));
        }

        return prop.land(equal_invalid_bv);
      }
    }
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    if(operands.size()==1 &&
       operands[0].type().id()==ID_pointer)
    {
      // we postpone
      literalt l=prop.new_variable();

      postponed_list.emplace_back(bvt{1, l}, convert_bv(operands[0]), expr);

      return l;
    }
  }
  else if(expr.id()==ID_lt || expr.id()==ID_le ||
          expr.id()==ID_gt || expr.id()==ID_ge)
  {
    if(operands.size()==2 &&
       operands[0].type().id()==ID_pointer &&
       operands[1].type().id()==ID_pointer)
    {
      const bvt &bv0=convert_bv(operands[0]);
      const bvt &bv1=convert_bv(operands[1]);

      const pointer_typet &type0 = to_pointer_type(operands[0].type());
      bvt offset_bv0 = offset_literals(bv0, type0);

      const pointer_typet &type1 = to_pointer_type(operands[1].type());
      bvt offset_bv1 = offset_literals(bv1, type1);

      // Comparison over pointers to distinct objects is undefined behavior in
      // C; we choose to always produce "false" in such a case.  Alternatively,
      // we could do a comparison over the integer representation of a pointer

      // do the same-object-test via an expression as this may permit re-using
      // already cached encodings of the equality test
      const exprt same_object = ::same_object(operands[0], operands[1]);
      const literalt same_object_lit = convert(same_object);
      if(same_object_lit.is_false())
        return same_object_lit;

      return prop.land(
        same_object_lit,
        bv_utils.rel(
          offset_bv0,
          expr.id(),
          offset_bv1,
          bv_utilst::representationt::SIGNED));
    }
  }

  return SUB::convert_rest(expr);
}

bv_pointerst::bv_pointerst(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &message_handler,
  bool get_array_constraints)
  : boolbvt(_ns, _prop, message_handler, get_array_constraints),
    pointer_logic(_ns)
{
}

optionalt<bvt> bv_pointerst::convert_address_of_rec(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    return add_addr(expr);
  }
  else if(expr.id()==ID_label)
  {
    return add_addr(expr);
  }
  else if(expr.id() == ID_null_object)
  {
    pointer_typet pt = pointer_type(expr.type());
    return encode(pointer_logic.get_null_object(), pt);
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &index=index_expr.index();
    const auto &array_type = to_array_type(array.type());

    pointer_typet type = pointer_type(expr.type());
    const std::size_t bits = boolbv_width(type);

    bvt bv;

    // recursive call
    if(array_type.id()==ID_pointer)
    {
      // this should be gone
      bv=convert_pointer_type(array);
      CHECK_RETURN(bv.size()==bits);
    }
    else if(array_type.id()==ID_array ||
            array_type.id()==ID_string_constant)
    {
      auto bv_opt = convert_address_of_rec(array);
      if(!bv_opt.has_value())
        return {};
      bv = std::move(*bv_opt);
      CHECK_RETURN(bv.size()==bits);
    }
    else
      UNREACHABLE;

    // get size
    auto size = pointer_offset_size(array_type.element_type(), ns);
    CHECK_RETURN(size.has_value() && *size >= 0);

    bv = offset_arithmetic(type, bv, *size, index);
    CHECK_RETURN(bv.size()==bits);

    return std::move(bv);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr=to_byte_extract_expr(expr);

    // recursive call
    auto bv_opt = convert_address_of_rec(byte_extract_expr.op());
    if(!bv_opt.has_value())
      return {};

    pointer_typet type = pointer_type(expr.type());
    const std::size_t bits = boolbv_width(type);
    CHECK_RETURN(bv_opt->size() == bits);

    bvt bv = offset_arithmetic(type, *bv_opt, 1, byte_extract_expr.offset());
    CHECK_RETURN(bv.size()==bits);
    return std::move(bv);
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    const exprt &struct_op = member_expr.compound();
    const typet &struct_op_type=ns.follow(struct_op.type());

    // recursive call
    auto bv_opt = convert_address_of_rec(struct_op);
    if(!bv_opt.has_value())
      return {};

    bvt bv = std::move(*bv_opt);
    if(struct_op_type.id()==ID_struct)
    {
      auto offset = member_offset(
        to_struct_type(struct_op_type), member_expr.get_component_name(), ns);
      CHECK_RETURN(offset.has_value());

      // add offset
      pointer_typet type = pointer_type(expr.type());
      bv = offset_arithmetic(type, bv, *offset);
    }
    else
    {
      INVARIANT(
        struct_op_type.id() == ID_union,
        "member expression should operate on struct or union");
      // nothing to do, all members have offset 0
    }

    return std::move(bv);
  }
  else if(expr.id()==ID_constant ||
          expr.id()==ID_string_constant ||
          expr.id()==ID_array)
  { // constant
    return add_addr(expr);
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &ifex=to_if_expr(expr);

    literalt cond=convert(ifex.cond());

    bvt bv1, bv2;

    auto bv1_opt = convert_address_of_rec(ifex.true_case());
    if(!bv1_opt.has_value())
      return {};

    auto bv2_opt = convert_address_of_rec(ifex.false_case());
    if(!bv2_opt.has_value())
      return {};

    return bv_utils.select(cond, *bv1_opt, *bv2_opt);
  }

  return {};
}

bvt bv_pointerst::convert_pointer_type(const exprt &expr)
{
  const pointer_typet &type = to_pointer_type(expr.type());

  const std::size_t bits = boolbv_width(expr.type());

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(expr).get_identifier();

    return map.get_literals(identifier, type, bits);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    return prop.new_variables(bits);
  }
  else if(expr.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr = to_typecast_expr(expr);

    const exprt &op = typecast_expr.op();
    const typet &op_type = op.type();

    if(op_type.id()==ID_pointer)
      return convert_bv(op);
    else if(
      can_cast_type<bitvector_typet>(op_type) || op_type.id() == ID_bool ||
      op_type.id() == ID_c_enum || op_type.id() == ID_c_enum_tag)
    {
      // Cast from a bitvector type to pointer.
      // We just do a zero extension.

      const bvt &op_bv=convert_bv(op);

      return bv_utils.zero_extension(op_bv, bits);
    }
  }
  else if(expr.id()==ID_if)
  {
    return SUB::convert_if(to_if_expr(expr));
  }
  else if(expr.id()==ID_index)
  {
    return SUB::convert_index(to_index_expr(expr));
  }
  else if(expr.id()==ID_member)
  {
    return SUB::convert_member(to_member_expr(expr));
  }
  else if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr = to_address_of_expr(expr);

    auto bv_opt = convert_address_of_rec(address_of_expr.op());
    if(!bv_opt.has_value())
      return conversion_failed(address_of_expr);

    CHECK_RETURN(bv_opt->size() == bits);
    return *bv_opt;
  }
  else if(expr.id()==ID_constant)
  {
    const constant_exprt &c = to_constant_expr(expr);

    if(is_null_pointer(c))
      return encode(pointer_logic.get_null_object(), type);
    else
    {
      mp_integer i = bvrep2integer(c.get_value(), bits, false);
      return bv_utils.build_constant(i, bits);
    }
  }
  else if(expr.id()==ID_plus)
  {
    // this has to be pointer plus integer

    const plus_exprt &plus_expr = to_plus_expr(expr);

    bvt bv;

    mp_integer size=0;
    std::size_t count=0;

    forall_operands(it, plus_expr)
    {
      if(it->type().id()==ID_pointer)
      {
        count++;
        bv=convert_bv(*it);
        CHECK_RETURN(bv.size()==bits);

        typet pointer_base_type = to_pointer_type(it->type()).base_type();

        if(pointer_base_type.id() == ID_empty)
        {
          // This is a gcc extension.
          // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
          size = 1;
        }
        else
        {
          auto size_opt = pointer_offset_size(pointer_base_type, ns);
          CHECK_RETURN(size_opt.has_value() && *size_opt >= 0);
          size = *size_opt;
        }
      }
    }

    INVARIANT(
      count == 1,
      "there should be exactly one pointer-type operand in a pointer-type sum");

    const std::size_t offset_bits = get_offset_width(type);
    bvt sum = bv_utils.build_constant(0, offset_bits);

    forall_operands(it, plus_expr)
    {
      if(it->type().id()==ID_pointer)
        continue;

      if(it->type().id()!=ID_unsignedbv &&
         it->type().id()!=ID_signedbv)
      {
        return conversion_failed(plus_expr);
      }

      bv_utilst::representationt rep=
        it->type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                     bv_utilst::representationt::UNSIGNED;

      bvt op=convert_bv(*it);
      CHECK_RETURN(!op.empty());

      op = bv_utils.extension(op, offset_bits, rep);

      sum=bv_utils.add(sum, op);
    }

    return offset_arithmetic(type, bv, size, sum);
  }
  else if(expr.id()==ID_minus)
  {
    // this is pointer-integer

    const minus_exprt &minus_expr = to_minus_expr(expr);

    INVARIANT(
      minus_expr.lhs().type().id() == ID_pointer,
      "first operand should be of pointer type");

    if(
      minus_expr.rhs().type().id() != ID_unsignedbv &&
      minus_expr.rhs().type().id() != ID_signedbv)
    {
      return conversion_failed(minus_expr);
    }

    const unary_minus_exprt neg_op1(minus_expr.rhs());

    const bvt &bv = convert_bv(minus_expr.lhs());

    typet pointer_base_type =
      to_pointer_type(minus_expr.lhs().type()).base_type();
    mp_integer element_size;

    if(pointer_base_type.id() == ID_empty)
    {
      // This is a gcc extension.
      // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
      element_size = 1;
    }
    else
    {
      auto element_size_opt = pointer_offset_size(pointer_base_type, ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
      element_size = *element_size_opt;
    }

    return offset_arithmetic(type, bv, element_size, neg_op1);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    return SUB::convert_byte_extract(to_byte_extract_expr(expr));
  }
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    return SUB::convert_byte_update(to_byte_update_expr(expr));
  }
  else if(expr.id() == ID_field_address)
  {
    const auto &field_address_expr = to_field_address_expr(expr);
    const typet &compound_type = ns.follow(field_address_expr.compound_type());

    // recursive call
    auto bv = convert_bitvector(field_address_expr.base());

    if(compound_type.id() == ID_struct)
    {
      auto offset = member_offset(
        to_struct_type(compound_type), field_address_expr.component_name(), ns);
      CHECK_RETURN(offset.has_value());

      // add offset
      bv = offset_arithmetic(field_address_expr.type(), bv, *offset);
    }
    else if(compound_type.id() == ID_union)
    {
      // nothing to do, all fields have offset 0
    }
    else
    {
      INVARIANT(false, "field address expressions operate on struct or union");
    }

    return bv;
  }
  else if(expr.id() == ID_element_address)
  {
    const auto &element_address_expr = to_element_address_expr(expr);

    // recursive call
    auto bv = convert_bitvector(element_address_expr.base());

    // get element size
    auto size = pointer_offset_size(element_address_expr.element_type(), ns);
    CHECK_RETURN(size.has_value() && *size >= 0);

    // add offset
    bv = offset_arithmetic(
      element_address_expr.type(), bv, *size, element_address_expr.index());

    return bv;
  }

  return conversion_failed(expr);
}

static bool is_pointer_subtraction(const exprt &expr)
{
  if(expr.id() != ID_minus)
    return false;

  const auto &minus_expr = to_minus_expr(expr);

  return minus_expr.lhs().type().id() == ID_pointer &&
         minus_expr.rhs().type().id() == ID_pointer;
}

bvt bv_pointerst::convert_bitvector(const exprt &expr)
{
  if(expr.type().id()==ID_pointer)
    return convert_pointer_type(expr);

  if(is_pointer_subtraction(expr))
  {
    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // pointer minus pointer is subtraction over the offset divided by element
    // size, iff the pointers point to the same object
    const auto &minus_expr = to_minus_expr(expr);

    // do the same-object-test via an expression as this may permit re-using
    // already cached encodings of the equality test
    const exprt same_object = ::same_object(minus_expr.lhs(), minus_expr.rhs());
    const literalt same_object_lit = convert(same_object);

    // compute the object size (again, possibly using cached results)
    const exprt object_size = ::object_size(minus_expr.lhs());
    const bvt object_size_bv =
      bv_utils.zero_extension(convert_bv(object_size), width);

    bvt bv = prop.new_variables(width);

    if(!same_object_lit.is_false())
    {
      const pointer_typet &lhs_pt = to_pointer_type(minus_expr.lhs().type());
      const bvt &lhs = convert_bv(minus_expr.lhs());
      const bvt lhs_offset =
        bv_utils.sign_extension(offset_literals(lhs, lhs_pt), width);

      const literalt lhs_in_bounds = prop.land(
        !bv_utils.sign_bit(lhs_offset),
        bv_utils.rel(
          lhs_offset,
          ID_le,
          object_size_bv,
          bv_utilst::representationt::UNSIGNED));

      const pointer_typet &rhs_pt = to_pointer_type(minus_expr.rhs().type());
      const bvt &rhs = convert_bv(minus_expr.rhs());
      const bvt rhs_offset =
        bv_utils.sign_extension(offset_literals(rhs, rhs_pt), width);

      const literalt rhs_in_bounds = prop.land(
        !bv_utils.sign_bit(rhs_offset),
        bv_utils.rel(
          rhs_offset,
          ID_le,
          object_size_bv,
          bv_utilst::representationt::UNSIGNED));

      bvt difference = bv_utils.sub(lhs_offset, rhs_offset);

      // Support for void* is a gcc extension, with the size treated as 1 byte
      // (no division required below).
      // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
      if(lhs_pt.base_type().id() != ID_empty)
      {
        auto element_size_opt = pointer_offset_size(lhs_pt.base_type(), ns);
        CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);

        if(*element_size_opt != 1)
        {
          bvt element_size_bv =
            bv_utils.build_constant(*element_size_opt, width);
          difference = bv_utils.divider(
            difference, element_size_bv, bv_utilst::representationt::SIGNED);
        }
      }

      prop.l_set_to_true(prop.limplies(
        prop.land(same_object_lit, prop.land(lhs_in_bounds, rhs_in_bounds)),
        bv_utils.equal(difference, bv)));
    }

    return bv;
  }
  else if(
    expr.id() == ID_pointer_offset &&
    to_pointer_offset_expr(expr).pointer().type().id() == ID_pointer)
  {
    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    const exprt &pointer = to_pointer_offset_expr(expr).pointer();
    const bvt &pointer_bv = convert_bv(pointer);

    bvt offset_bv =
      offset_literals(pointer_bv, to_pointer_type(pointer.type()));

    // we do a sign extension to permit negative offsets
    return bv_utils.sign_extension(offset_bv, width);
  }
  else if(
    const auto object_size = expr_try_dynamic_cast<object_size_exprt>(expr))
  {
    // we postpone until we know the objects
    std::size_t width = boolbv_width(object_size->type());

    postponed_list.emplace_back(
      prop.new_variables(width),
      convert_bv(object_size->pointer()),
      *object_size);

    return postponed_list.back().bv;
  }
  else if(
    expr.id() == ID_pointer_object &&
    to_pointer_object_expr(expr).pointer().type().id() == ID_pointer)
  {
    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    const exprt &pointer = to_pointer_object_expr(expr).pointer();
    const bvt &pointer_bv = convert_bv(pointer);

    bvt object_bv =
      object_literals(pointer_bv, to_pointer_type(pointer.type()));

    return bv_utils.zero_extension(object_bv, width);
  }
  else if(
    expr.id() == ID_typecast &&
    to_typecast_expr(expr).op().type().id() == ID_pointer)
  {
    // pointer to int
    bvt op0 = convert_pointer_type(to_typecast_expr(expr).op());

    // squeeze it in!

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    return bv_utils.zero_extension(op0, width);
  }
  else if(expr.id() == ID_object_address)
  {
    const auto &object_address_expr = to_object_address_expr(expr);
    return add_addr(object_address_expr.object_expr());
  }

  return SUB::convert_bitvector(expr);
}

static std::string bits_to_string(const propt &prop, const bvt &bv)
{
  std::string result;

  for(const auto &literal : bv)
  {
    char ch=0;

    // clang-format off
    switch(prop.l_get(literal).get_value())
    {
    case tvt::tv_enumt::TV_FALSE: ch = '0'; break;
    case tvt::tv_enumt::TV_TRUE: ch = '1'; break;
    case tvt::tv_enumt::TV_UNKNOWN: ch = '0'; break;
    }
    // clang-format on

    result = ch + result;
  }

  return result;
}

exprt bv_pointerst::bv_get_rec(
  const exprt &expr,
  const bvt &bv,
  std::size_t offset,
  const typet &type) const
{
  if(type.id() != ID_pointer)
    return SUB::bv_get_rec(expr, bv, offset, type);

  const pointer_typet &pt = to_pointer_type(type);
  const std::size_t bits = boolbv_width(pt);
  bvt value_bv(bv.begin() + offset, bv.begin() + offset + bits);

  std::string value = bits_to_string(prop, value_bv);
  std::string value_addr = bits_to_string(prop, object_literals(value_bv, pt));
  std::string value_offset =
    bits_to_string(prop, offset_literals(value_bv, pt));

  // we treat these like bit-vector constants, but with
  // some additional annotation

  const irep_idt bvrep = make_bvrep(bits, [&value](std::size_t i) {
    return value[value.size() - 1 - i] == '1';
  });

  constant_exprt result(bvrep, type);

  pointer_logict::pointert pointer;
  pointer.object =
    numeric_cast_v<std::size_t>(binary2integer(value_addr, false));
  pointer.offset=binary2integer(value_offset, true);

  return annotated_pointer_constant_exprt{
    bvrep, pointer_logic.pointer_expr(pointer, pt)};
}

bvt bv_pointerst::encode(std::size_t addr, const pointer_typet &type) const
{
  const std::size_t offset_bits = get_offset_width(type);
  const std::size_t object_bits = get_object_width(type);

  bvt zero_offset(offset_bits, const_literal(false));

  // set variable part
  bvt object;
  object.reserve(object_bits);
  for(std::size_t i=0; i<object_bits; i++)
    object.push_back(const_literal((addr & (std::size_t(1) << i)) != 0));

  return object_offset_encoding(object, zero_offset);
}

bvt bv_pointerst::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &x)
{
  const std::size_t offset_bits = get_offset_width(type);

  return offset_arithmetic(
    type, bv, 1, bv_utils.build_constant(x, offset_bits));
}

bvt bv_pointerst::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &factor,
  const exprt &index)
{
  bvt bv_index=convert_bv(index);

  bv_utilst::representationt rep=
    index.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                   bv_utilst::representationt::UNSIGNED;

  const std::size_t offset_bits = get_offset_width(type);
  bv_index=bv_utils.extension(bv_index, offset_bits, rep);

  return offset_arithmetic(type, bv, factor, bv_index);
}

bvt bv_pointerst::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &factor,
  const bvt &index)
{
  bvt bv_index;

  if(factor==1)
    bv_index=index;
  else
  {
    bvt bv_factor=bv_utils.build_constant(factor, index.size());
    bv_index = bv_utils.signed_multiplier(index, bv_factor);
  }

  const std::size_t offset_bits = get_offset_width(type);
  bv_index = bv_utils.sign_extension(bv_index, offset_bits);

  bvt offset_bv = offset_literals(bv, type);

  bvt bv_tmp = bv_utils.add(offset_bv, bv_index);

  return object_offset_encoding(object_literals(bv, type), bv_tmp);
}

bvt bv_pointerst::add_addr(const exprt &expr)
{
  std::size_t a=pointer_logic.add_object(expr);

  const pointer_typet type = pointer_type(expr.type());
  const std::size_t object_bits = get_object_width(type);
  const std::size_t max_objects=std::size_t(1)<<object_bits;

  if(a==max_objects)
    throw analysis_exceptiont(
      "too many addressed objects: maximum number of objects is set to 2^n=" +
      std::to_string(max_objects) + " (with n=" + std::to_string(object_bits) +
      "); " +
      "use the `--object-bits n` option to increase the maximum number");

  return encode(a, type);
}

void bv_pointerst::do_postponed(
  const postponedt &postponed)
{
  if(postponed.expr.id() == ID_is_dynamic_object)
  {
    const auto &type =
      to_pointer_type(to_unary_expr(postponed.expr).op().type());
    const auto &objects = pointer_logic.objects;
    std::size_t number=0;

    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
    {
      const exprt &expr=*it;

      bool is_dynamic=pointer_logic.is_dynamic_object(expr);

      // only compare object part
      pointer_typet pt = pointer_type(expr.type());
      bvt bv = object_literals(encode(number, pt), type);

      bvt saved_bv = object_literals(postponed.op, type);

      POSTCONDITION(bv.size()==saved_bv.size());
      PRECONDITION(postponed.bv.size()==1);

      literalt l1=bv_utils.equal(bv, saved_bv);
      literalt l2=postponed.bv.front();

      if(!is_dynamic)
        l2=!l2;

      prop.l_set_to_true(prop.limplies(l1, l2));
    }
  }
  else if(
    const auto postponed_object_size =
      expr_try_dynamic_cast<object_size_exprt>(postponed.expr))
  {
    const auto &type = to_pointer_type(postponed_object_size->pointer().type());
    const auto &objects = pointer_logic.objects;
    std::size_t number=0;

    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
    {
      const exprt &expr=*it;

      if(expr.id() != ID_symbol && expr.id() != ID_string_constant)
        continue;

      const auto size_expr = size_of_expr(expr.type(), ns);

      if(!size_expr.has_value())
        continue;

      const exprt object_size = typecast_exprt::conditional_cast(
        size_expr.value(), postponed_object_size->type());

      // only compare object part
      pointer_typet pt = pointer_type(expr.type());
      bvt bv = object_literals(encode(number, pt), type);

      bvt saved_bv = object_literals(postponed.op, type);

      bvt size_bv = convert_bv(object_size);

      POSTCONDITION(bv.size()==saved_bv.size());
      PRECONDITION(postponed.bv.size()>=1);
      PRECONDITION(size_bv.size() == postponed.bv.size());

      literalt l1=bv_utils.equal(bv, saved_bv);
      literalt l2=bv_utils.equal(postponed.bv, size_bv);

      prop.l_set_to_true(prop.limplies(l1, l2));
    }
  }
  else
    UNREACHABLE;
}

void bv_pointerst::finish_eager_conversion()
{
  // post-processing arrays may yield further objects, do this first
  SUB::finish_eager_conversion();

  for(postponed_listt::const_iterator
      it=postponed_list.begin();
      it!=postponed_list.end();
      it++)
    do_postponed(*it);

  // Clear the list to avoid re-doing in case of incremental usage.
  postponed_list.clear();
}
