/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_pointers.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>

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
        bvt invalid_bv;
        encode(pointer_logic.get_invalid_object(), invalid_bv);

        const pointer_typet &type = to_pointer_type(operands[0].type());
        const std::size_t object_bits = boolbv_width.get_object_width(type);
        const std::size_t offset_bits = boolbv_width.get_offset_width(type);

        bvt equal_invalid_bv;
        equal_invalid_bv.resize(object_bits);

        for(std::size_t i=0; i<object_bits; i++)
        {
          equal_invalid_bv[i]=prop.lequal(bv[offset_bits+i],
                                          invalid_bv[offset_bits+i]);
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

      postponed_list.push_back(postponedt());
      postponed_list.back().op = convert_bv(operands[0]);
      postponed_list.back().bv.push_back(l);
      postponed_list.back().expr = expr;

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
      // comparison over integers
      bvt bv0 = convert_bv(operands[0]);
      address_bv(bv0, to_pointer_type(operands[0].type()));
      bvt bv1 = convert_bv(operands[1]);
      address_bv(bv1, to_pointer_type(operands[1].type()));

      return bv_utils.rel(
        bv0, expr.id(), bv1, bv_utilst::representationt::UNSIGNED);
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
    pointer_logic(_ns),
    need_address_bounds(false)
{
  const pointer_typet type = pointer_type(empty_typet());

  // the address of NULL is zero unless the platform uses a different
  // configuration, in which case we use a non-deterministic integer
  // value
  bvt &null_pointer = pointer_bits[pointer_logic.get_null_object()];
  null_pointer.resize(
    boolbv_width.get_address_width(type), const_literal(false));
  if(!pointer_logic.get_null_is_zero())
  {
    for(auto &literal : null_pointer)
      literal = prop.new_variable();
  }

  // use the maximum integer as the address of an invalid object,
  // unless NULL is not zero on this platform (and might thus be this
  // maximum integer), in which case we use a non-deterministic
  // integer value
  bvt &invalid_object = pointer_bits[pointer_logic.get_invalid_object()];
  invalid_object.resize(
    boolbv_width.get_address_width(type), const_literal(true));
  if(!pointer_logic.get_null_is_zero())
  {
    for(auto &literal : invalid_object)
      literal = prop.new_variable();

    // NULL and INVALID are distinct
    prop.l_set_to_false(bv_utils.equal(null_pointer, invalid_object));
  }
}

bool bv_pointerst::convert_address_of_rec(
  const exprt &expr,
  bvt &bv)
{
  if(expr.id()==ID_symbol)
  {
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id()==ID_label)
  {
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id() == ID_null_object)
  {
    encode(pointer_logic.get_null_object(), bv);
    return false;
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &index=index_expr.index();
    const typet &array_type = array.type();

    const std::size_t bits = boolbv_width(pointer_type(empty_typet()));

    // recursive call
    if(array_type.id()==ID_pointer)
    {
      // this should be gone
      bv = convert_bv(array);
      CHECK_RETURN(bv.size()==bits);
    }
    else if(array_type.id()==ID_array ||
            array_type.id()==ID_string_constant)
    {
      if(convert_address_of_rec(array, bv))
        return true;
      CHECK_RETURN(bv.size()==bits);
    }
    else
      UNREACHABLE;

    // get size
    auto size = pointer_offset_size(array_type.subtype(), ns);
    CHECK_RETURN(size.has_value() && *size >= 0);

    offset_arithmetic(bv, *size, index);
    CHECK_RETURN(bv.size()==bits);
    return false;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr=to_byte_extract_expr(expr);

    // recursive call
    if(convert_address_of_rec(byte_extract_expr.op(), bv))
      return true;

    const std::size_t bits = boolbv_width(pointer_type(empty_typet()));
    CHECK_RETURN(bv.size()==bits);

    offset_arithmetic(bv, 1, byte_extract_expr.offset());
    CHECK_RETURN(bv.size()==bits);
    return false;
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    const exprt &struct_op = member_expr.compound();
    const typet &struct_op_type=ns.follow(struct_op.type());

    // recursive call
    if(convert_address_of_rec(struct_op, bv))
      return true;

    if(struct_op_type.id()==ID_struct)
    {
      auto offset = member_offset(
        to_struct_type(struct_op_type), member_expr.get_component_name(), ns);
      CHECK_RETURN(offset.has_value());

      // add offset
      offset_arithmetic(bv, *offset);
    }
    else
    {
      INVARIANT(
        struct_op_type.id() == ID_union,
        "member expression should operate on struct or union");
      // nothing to do, all members have offset 0
    }

    return false;
  }
  else if(expr.id()==ID_constant ||
          expr.id()==ID_string_constant ||
          expr.id()==ID_array)
  { // constant
    add_addr(expr, bv);
    return false;
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &ifex=to_if_expr(expr);

    literalt cond=convert(ifex.cond());

    bvt bv1, bv2;

    if(convert_address_of_rec(ifex.true_case(), bv1))
      return true;

    if(convert_address_of_rec(ifex.false_case(), bv2))
      return true;

    bv=bv_utils.select(cond, bv1, bv2);

    return false;
  }

  return true;
}

bvt bv_pointerst::convert_pointer_type(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_pointer);

  const std::size_t bits = boolbv_width(expr.type());

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(expr).get_identifier();
    const typet &type=expr.type();

    return map.get_literals(identifier, type, bits);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    bvt bv;
    bv.resize(bits);

    for(auto &literal : bv)
      literal = prop.new_variable();

    return bv;
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

      // Fixed integer address is NULL object plus given offset.
      if(op.id() == ID_constant)
      {
        bvt bv;

        encode(pointer_logic.get_null_object(), bv);
        offset_arithmetic(bv, 1, op);

        return bv;
      }

      // For all other cases we postpone until we know the full set of objects.
      std::size_t width =
        boolbv_width.get_offset_width(to_pointer_type(expr.type())) +
        boolbv_width.get_object_width(to_pointer_type(expr.type()));

      bvt bv;
      bv.resize(width);

      for(std::size_t i = 0; i < width; i++)
        bv[i] = prop.new_variable();

      bvt op_bv = convert_bv(op);
      bv_utilst::representationt rep = op_type.id() == ID_signedbv
                                         ? bv_utilst::representationt::SIGNED
                                         : bv_utilst::representationt::UNSIGNED;

      DATA_INVARIANT(
        op_bv.size() <=
          boolbv_width.get_address_width(to_pointer_type(expr.type())),
        "integer cast to pointer of smaller size");
      op_bv = bv_utils.extension(
        op_bv,
        boolbv_width.get_address_width(to_pointer_type(expr.type())),
        rep);

      bv.insert(bv.end(), op_bv.begin(), op_bv.end());

      postponed_list.push_back(postponedt());
      postponed_list.back().op = op_bv;
      postponed_list.back().bv = bv;
      postponed_list.back().expr = expr;

      DATA_INVARIANT(
        postponed_list.back().bv.size() == bits,
        "pointer encoding does not have matching width");

      return postponed_list.back().bv;
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

    bvt bv;
    bv.resize(bits);

    if(convert_address_of_rec(address_of_expr.op(), bv))
    {
      conversion_failed(address_of_expr, bv);
      return bv;
    }

    CHECK_RETURN(bv.size()==bits);
    return bv;
  }
  else if(expr.id()==ID_constant)
  {
    irep_idt value=to_constant_expr(expr).get_value();

    bvt bv;
    bv.resize(bits);

    if(value==ID_NULL)
      encode(pointer_logic.get_null_object(), bv);
    else
    {
      mp_integer i = bvrep2integer(value, bits, false);
      bvt bv_offset = bv_utils.build_constant(
        i, boolbv_width.get_offset_width(to_pointer_type(expr.type())));
      bvt bv_addr = bv_utils.build_constant(
        i, boolbv_width.get_address_width(to_pointer_type(expr.type())));

      encode(pointer_logic.get_invalid_object(), bv);
      object_bv(bv, to_pointer_type(expr.type()));
      bv.insert(bv.end(), bv_offset.begin(), bv_offset.end());
      bv.insert(bv.end(), bv_addr.begin(), bv_addr.end());

      DATA_INVARIANT(
        bv.size() == bits, "pointer encoding does not have matching width");
    }

    return bv;
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

        typet pointer_sub_type=it->type().subtype();

        if(pointer_sub_type.id()==ID_empty)
        {
          // This is a gcc extension.
          // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
          size = 1;
        }
        else
        {
          auto size_opt = pointer_offset_size(pointer_sub_type, ns);
          CHECK_RETURN(size_opt.has_value() && *size_opt >= 0);
          size = *size_opt;
        }
      }
    }

    INVARIANT(
      count == 1,
      "there should be exactly one pointer-type operand in a pointer-type sum");

    exprt sum = plus_expr;
    for(exprt::operandst::iterator it = sum.operands().begin();
        it != sum.operands().end();) // no ++it
    {
      if(it->type().id()==ID_pointer)
      {
        it = sum.operands().erase(it);
        continue;
      }

      if(it->type().id()!=ID_unsignedbv &&
         it->type().id()!=ID_signedbv)
      {
        bvt failed_bv;
        conversion_failed(plus_expr, failed_bv);
        return failed_bv;
      }

      sum.type() = it->type();
      ++it;
    }
    CHECK_RETURN(!sum.operands().empty());
    if(sum.operands().size() == 1)
    {
      exprt tmp = sum.operands().front();
      sum.swap(tmp);
    }

    offset_arithmetic(bv, size, sum);

    return bv;
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
      bvt bv;
      conversion_failed(minus_expr, bv);
      return bv;
    }

    const unary_minus_exprt neg_op1(minus_expr.rhs());

    bvt bv = convert_bv(minus_expr.lhs());

    typet pointer_sub_type = minus_expr.rhs().type().subtype();
    mp_integer element_size;

    if(pointer_sub_type.id()==ID_empty)
    {
      // This is a gcc extension.
      // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
      element_size = 1;
    }
    else
    {
      auto element_size_opt = pointer_offset_size(pointer_sub_type, ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
      element_size = *element_size_opt;
    }

    offset_arithmetic(bv, element_size, neg_op1);

    return bv;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    return SUB::convert_byte_extract(to_byte_extract_expr(expr));
  }
  else
  {
    return SUB::convert_byte_update(to_byte_update_expr(expr));
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
    // pointer minus pointer
    const auto &minus_expr = to_minus_expr(expr);
    bvt lhs = convert_bv(minus_expr.lhs());
    bvt rhs = convert_bv(minus_expr.rhs());

    // this is address arithmetic, but does consider the type
    address_bv(lhs, to_pointer_type(minus_expr.lhs().type()));
    address_bv(rhs, to_pointer_type(minus_expr.rhs().type()));

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // we do a zero extension
    lhs = bv_utils.zero_extension(lhs, width);
    rhs = bv_utils.zero_extension(rhs, width);

    bvt bv = bv_utils.sub(lhs, rhs);

    typet pointer_sub_type = minus_expr.lhs().type().subtype();
    mp_integer element_size;

    if(pointer_sub_type.id()==ID_empty)
    {
      // This is a gcc extension.
      // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
      element_size = 1;
    }
    else
    {
      auto element_size_opt = pointer_offset_size(pointer_sub_type, ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
      element_size = *element_size_opt;
    }

    if(element_size != 1)
    {
      bvt element_size_bv = bv_utils.build_constant(element_size, bv.size());
      bv=bv_utils.divider(
        bv, element_size_bv, bv_utilst::representationt::SIGNED);
    }

    return bv;
  }
  else if(
    expr.id() == ID_pointer_offset &&
    to_unary_expr(expr).op().type().id() == ID_pointer)
  {
    const exprt &op0 = to_unary_expr(expr).op();
    bvt op0_bv = convert_bv(op0);

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // we need to strip off the object part
    offset_bv(op0_bv, to_pointer_type(op0.type()));

    // we do a sign extension to permit negative offsets
    return bv_utils.sign_extension(op0_bv, width);
  }
  else if(
    expr.id() == ID_object_size &&
    to_unary_expr(expr).op().type().id() == ID_pointer)
  {
    // we postpone until we know the objects
    std::size_t width=boolbv_width(expr.type());

    bvt bv;
    bv.resize(width);

    for(std::size_t i=0; i<width; i++)
      bv[i]=prop.new_variable();

    postponed_list.push_back(postponedt());

    postponed_list.back().op = convert_bv(to_unary_expr(expr).op());
    postponed_list.back().bv=bv;
    postponed_list.back().expr=expr;

    return bv;
  }
  else if(
    expr.id() == ID_pointer_object &&
    to_unary_expr(expr).op().type().id() == ID_pointer)
  {
    const exprt &op0 = to_unary_expr(expr).op();
    bvt op0_bv = convert_bv(op0);

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    // erase offset and integer bits
    object_bv(op0_bv, to_pointer_type(op0.type()));

    return bv_utils.zero_extension(op0_bv, width);
  }
  else if(
    expr.id() == ID_typecast &&
    to_typecast_expr(expr).op().type().id() == ID_pointer)
  {
    // pointer to int
    bvt op0 = convert_bv(to_typecast_expr(expr).op());

    // erase offset and object bits
    address_bv(op0, to_pointer_type(to_typecast_expr(expr).op().type()));

    std::size_t width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr);

    need_address_bounds = true;

    return bv_utils.zero_extension(op0, width);
  }

  return SUB::convert_bitvector(expr);
}

exprt bv_pointerst::bv_get_rec(
  const exprt &expr,
  const bvt &bv,
  std::size_t offset,
  const typet &type) const
{
  if(type.id()!=ID_pointer)
    return SUB::bv_get_rec(expr, bv, offset, type);

  std::string value, value_offset, value_obj;

  const std::size_t object_bits =
    boolbv_width.get_object_width(to_pointer_type(type));
  const std::size_t offset_bits =
    boolbv_width.get_offset_width(to_pointer_type(type));
  const std::size_t address_bits =
    boolbv_width.get_address_width(to_pointer_type(type));
  for(std::size_t i = 0; i < object_bits + offset_bits + address_bits; i++)
  {
    char ch=0;
    std::size_t bit_nr=i+offset;

    // clang-format off
    switch(prop.l_get(bv[bit_nr]).get_value())
    {
    case tvt::tv_enumt::TV_FALSE: ch = '0'; break;
    case tvt::tv_enumt::TV_TRUE: ch = '1'; break;
    case tvt::tv_enumt::TV_UNKNOWN: ch = '0'; break;
    }
    // clang-format on

    if(i < object_bits)
      value_obj = ch + value_obj;
    else if(i < object_bits + offset_bits)
      value_offset = ch + value_offset;
    else
      value = ch + value;
  }

  // we treat these like bit-vector constants, but with
  // some additional annotation

  const irep_idt bvrep = make_bvrep(address_bits, [&value](std::size_t i) {
    return value[value.size() - 1 - i] == '1';
  });

  constant_exprt result(bvrep, type);

  pointer_logict::pointert pointer;
  pointer.object =
    numeric_cast_v<std::size_t>(binary2integer(value_obj, false));
  pointer.offset=binary2integer(value_offset, true);

  // we add the elaborated expression as operand
  result.copy_to_operands(
    pointer_logic.pointer_expr(pointer, to_pointer_type(type)));

  return std::move(result);
}

void bv_pointerst::encode(std::size_t addr, bvt &bv)
{
  const pointer_typet type = pointer_type(empty_typet());
  const std::size_t offset_bits = boolbv_width.get_offset_width(type);
  const std::size_t object_bits = boolbv_width.get_object_width(type);
  const std::size_t address_bits = boolbv_width.get_object_width(type);
  const std::size_t bits = offset_bits + object_bits + address_bits;
  PRECONDITION(boolbv_width(type) == bits);

  bv.clear();
  bv.reserve(bits);

  // set variable part
  for(std::size_t i=0; i<object_bits; i++)
    bv.push_back(const_literal((addr & (std::size_t(1) << i)) != 0));

  // set offset to zero
  for(std::size_t i = 0; i < offset_bits; i++)
    bv.push_back(const_literal(false));

  // add integer value
  auto entry = pointer_bits.insert({addr, bvt()});
  if(entry.second)
  {
    entry.first->second.reserve(address_bits);
    for(unsigned i = 0; i < address_bits; ++i)
      entry.first->second.push_back(prop.new_variable());
  }

  bv.insert(bv.end(), entry.first->second.begin(), entry.first->second.end());

  DATA_INVARIANT(
    bv.size() == bits, "pointer encoding does not have matching width");
}

void bv_pointerst::offset_arithmetic(bvt &bv, const mp_integer &x)
{
  const pointer_typet type = pointer_type(empty_typet());
  const std::size_t offset_bits = boolbv_width.get_offset_width(type);
  const std::size_t object_bits = boolbv_width.get_object_width(type);
  const std::size_t address_bits = boolbv_width.get_object_width(type);

  // add to offset_bits
  bvt bv1=bv;
  offset_bv(bv1, type);

  bvt bv2=bv_utils.build_constant(x, offset_bits);

  bvt tmp=bv_utils.add(bv1, bv2);

  // update offset bits
  for(std::size_t i=0; i<offset_bits; i++)
    bv[object_bits + i] = tmp[i];

  // add to pointer value
  bvt bv3 = bv;
  address_bv(bv3, type);

  bvt bv4 = bv_utils.build_constant(x, address_bits);

  bvt tmp2 = bv_utils.add(bv3, bv4);

  // update pointer value by offset
  for(std::size_t i = 0; i < address_bits; i++)
    bv[object_bits + offset_bits + i] = tmp2[i];
}

void bv_pointerst::offset_arithmetic(
  bvt &bv,
  const mp_integer &factor,
  const exprt &index)
{
  const pointer_typet type = pointer_type(empty_typet());
  const std::size_t offset_bits = boolbv_width.get_offset_width(type);
  const std::size_t object_bits = boolbv_width.get_object_width(type);
  const std::size_t address_bits = boolbv_width.get_object_width(type);

  bvt bv_index=convert_bv(index);

  bv_utilst::representationt rep=
    index.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                   bv_utilst::representationt::UNSIGNED;

  DATA_INVARIANT(
    bv_index.size() <= offset_bits,
    "pointer arithmetic does not have matching width");
  bv_index=bv_utils.extension(bv_index, offset_bits, rep);

  if(factor != 1)
  {
    bvt bv_factor = bv_utils.build_constant(factor, offset_bits);
    bv_index = bv_utils.signed_multiplier(bv_index, bv_factor);
  }

  // add to offset_bits
  bvt bv1 = bv;
  offset_bv(bv1, type);

  bvt bv_tmp = bv_utils.add(bv1, bv_index);

  // update offset bits
  for(std::size_t i=0; i<offset_bits; i++)
    bv[object_bits + i] = bv_tmp[i];

  // add to pointer value
  bvt bv2 = bv;
  address_bv(bv2, type);

  bv_index = bv_utils.zero_extension(bv_index, address_bits);

  bvt tmp2 = bv_utils.add(bv2, bv_index);

  // update pointer value by offset
  for(std::size_t i = 0; i < address_bits; i++)
    bv[object_bits + offset_bits + i] = tmp2[i];
}

void bv_pointerst::add_addr(const exprt &expr, bvt &bv)
{
  std::size_t a=pointer_logic.add_object(expr);

  const pointer_typet type = pointer_type(expr.type());
  const std::size_t object_bits = boolbv_width.get_object_width(type);
  const std::size_t max_objects=std::size_t(1)<<object_bits;

  if(a==max_objects)
    throw analysis_exceptiont(
      "too many addressed objects: maximum number of objects is set to 2^n=" +
      std::to_string(max_objects) + " (with n=" +
      std::to_string(boolbv_width.get_object_width(type)) + "); " +
      "use the `--object-bits n` option to increase the maximum number");

  auto entry = pointer_bits.insert({a, bvt()});
  if(entry.second)
  {
    std::size_t address_bits = boolbv_width.get_address_width(type);

    entry.first->second.reserve(address_bits);
    for(unsigned i = 0; i < address_bits; ++i)
      entry.first->second.push_back(prop.new_variable());
  }

  encode(a, bv);
}

void bv_pointerst::do_postponed_non_typecast(const postponedt &postponed)
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
      bvt bv;
      encode(number, bv);
      object_bv(bv, type);

      bvt saved_bv=postponed.op;
      object_bv(saved_bv, type);

      POSTCONDITION(bv.size()==saved_bv.size());
      PRECONDITION(postponed.bv.size()==1);

      literalt l1=bv_utils.equal(bv, saved_bv);
      literalt l2=postponed.bv.front();

      if(!is_dynamic)
        l2=!l2;

      prop.l_set_to_true(prop.limplies(l1, l2));
    }
  }
  else if(postponed.expr.id()==ID_object_size)
  {
    const auto &type =
      to_pointer_type(to_unary_expr(postponed.expr).op().type());
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
        size_expr.value(), postponed.expr.type());

      // only compare object part
      bvt bv;
      encode(number, bv);
      object_bv(bv, type);

      bvt saved_bv=postponed.op;
      object_bv(saved_bv, type);

      bvt size_bv = convert_bv(object_size);

      POSTCONDITION(bv.size()==saved_bv.size());
      PRECONDITION(postponed.bv.size()>=1);
      PRECONDITION(size_bv.size() == postponed.bv.size());

      literalt l1=bv_utils.equal(bv, saved_bv);

      literalt l2=bv_utils.equal(postponed.bv, size_bv);

      prop.l_set_to_true(prop.limplies(l1, l2));
    }
  }
  else if(postponed.expr.id() == ID_typecast)
  {
    // defer until phase 2 as the other postponed expressions may
    // yield additional entries in pointer_bits
    need_address_bounds = true;
  }
  else
    UNREACHABLE;
}

void bv_pointerst::encode_object_bounds(bounds_mapt &dest)
{
  const auto &objects = pointer_logic.objects;
  std::size_t number = 0;

  const bvt null_pointer = pointer_bits.at(pointer_logic.get_null_object());
  const bvt &invalid_object =
    pointer_bits.at(pointer_logic.get_invalid_object());

  bvt conj;
  conj.reserve(objects.size());

  for(const exprt &expr : objects)
  {
    const auto size_expr = size_of_expr(expr.type(), ns);

    if(!size_expr.has_value())
    {
      ++number;
      continue;
    }

    bvt size_bv = convert_bv(*size_expr);

    // NULL, INVALID have no size
    DATA_INVARIANT(
      number != pointer_logic.get_null_object(),
      "NULL object cannot have a size");
    DATA_INVARIANT(
      number != pointer_logic.get_invalid_object(),
      "INVALID object cannot have a size");

    bvt object_bv;
    encode(number, object_bv);

    // prepare comparison over integers
    bvt bv = object_bv;
    address_bv(bv, pointer_type(expr.type()));
    DATA_INVARIANT(
      bv.size() == null_pointer.size(),
      "NULL pointer encoding does not have matching width");
    DATA_INVARIANT(
      bv.size() == invalid_object.size(),
      "INVALID pointer encoding does not have matching width");
    DATA_INVARIANT(
      size_bv.size() == bv.size(),
      "pointer encoding does not have matching width");

    // NULL, INVALID must not be within object bounds
    literalt null_lower_bound = bv_utils.rel(
      null_pointer, ID_lt, bv, bv_utilst::representationt::UNSIGNED);

    literalt inv_obj_lower_bound = bv_utils.rel(
      invalid_object, ID_lt, bv, bv_utilst::representationt::UNSIGNED);

    // compute the upper bound with the side effect of enforcing the
    // object addresses not to wrap around/overflow
    bvt obj_upper_bound = bv_utils.add_sub_no_overflow(
      bv, size_bv, false, bv_utilst::representationt::UNSIGNED);

    literalt null_upper_bound = bv_utils.rel(
      null_pointer,
      ID_ge,
      obj_upper_bound,
      bv_utilst::representationt::UNSIGNED);

    literalt inv_obj_upper_bound = bv_utils.rel(
      invalid_object,
      ID_ge,
      obj_upper_bound,
      bv_utilst::representationt::UNSIGNED);

    // store bounds for re-use
    dest.insert({number, {bv, obj_upper_bound}});

    conj.push_back(prop.lor(null_lower_bound, null_upper_bound));
    conj.push_back(prop.lor(inv_obj_lower_bound, inv_obj_upper_bound));

    ++number;
  }

  if(!conj.empty())
    prop.l_set_to_true(prop.land(conj));
}

void bv_pointerst::do_postponed_typecast(
  const postponedt &postponed,
  const bounds_mapt &bounds)
{
  if(postponed.expr.id() != ID_typecast)
    return;

  const pointer_typet &type = to_pointer_type(postponed.expr.type());
  const std::size_t bits = boolbv_width.get_offset_width(type) +
                           boolbv_width.get_object_width(type) +
                           boolbv_width.get_address_width(type);

  // given an integer (possibly representing an address) postponed.op,
  // compute the object and offset that it may refer to
  bvt saved_bv = postponed.op;

  bvt conj, oob_conj;
  conj.reserve(bounds.size() + 3);
  oob_conj.reserve(bounds.size());

  for(const auto &bounds_entry : bounds)
  {
    std::size_t number = bounds_entry.first;

    // pointer must be within object bounds
    const bvt &lb = bounds_entry.second.first;
    const bvt &ub = bounds_entry.second.second;

    literalt lower_bound =
      bv_utils.rel(saved_bv, ID_ge, lb, bv_utilst::representationt::UNSIGNED);

    literalt upper_bound =
      bv_utils.rel(saved_bv, ID_lt, ub, bv_utilst::representationt::UNSIGNED);

    // compute the offset within the object, and the corresponding
    // pointer bv
    bvt offset = bv_utils.sub(saved_bv, lb);

    bvt bv;
    encode(number, bv);
    object_bv(bv, type);
    DATA_INVARIANT(
      offset.size() == boolbv_width.get_offset_width(type),
      "pointer encoding does not have matching width");
    bv.insert(bv.end(), offset.begin(), offset.end());
    bv.insert(bv.end(), saved_bv.begin(), saved_bv.end());
    DATA_INVARIANT(
      bv.size() == bits, "pointer encoding does not have matching width");

    // if the integer address is within the object bounds, return an
    // adjusted offset
    literalt in_bounds = prop.land(lower_bound, upper_bound);
    conj.push_back(prop.limplies(in_bounds, bv_utils.equal(bv, postponed.bv)));
    oob_conj.push_back(!in_bounds);
  }

  // append integer address as both offset and address
  bvt invalid_bv, null_bv;
  encode(pointer_logic.get_invalid_object(), invalid_bv);
  object_bv(invalid_bv, type);
  invalid_bv.insert(invalid_bv.end(), saved_bv.begin(), saved_bv.end());
  invalid_bv.insert(invalid_bv.end(), saved_bv.begin(), saved_bv.end());
  encode(pointer_logic.get_null_object(), null_bv);
  object_bv(null_bv, type);
  null_bv.insert(null_bv.end(), saved_bv.begin(), saved_bv.end());
  null_bv.insert(null_bv.end(), saved_bv.begin(), saved_bv.end());

  // NULL is always NULL
  conj.push_back(prop.limplies(
    bv_utils.equal(saved_bv, pointer_bits.at(pointer_logic.get_null_object())),
    bv_utils.equal(null_bv, postponed.bv)));

  // INVALID is always INVALID
  conj.push_back(prop.limplies(
    bv_utils.equal(
      saved_bv, pointer_bits.at(pointer_logic.get_invalid_object())),
    bv_utils.equal(invalid_bv, postponed.bv)));

  // one of the objects or NULL or INVALID with an offset
  conj.push_back(prop.limplies(
    prop.land(oob_conj),
    prop.lor(
      bv_utils.equal(null_bv, postponed.bv),
      bv_utils.equal(invalid_bv, postponed.bv))));

  prop.l_set_to_true(prop.land(conj));
}

void bv_pointerst::post_process()
{
  // post-processing arrays may yield further objects, do this first
  SUB::post_process();

  for(postponed_listt::const_iterator
      it=postponed_list.begin();
      it!=postponed_list.end();
      it++)
    do_postponed_non_typecast(*it);

  if(need_address_bounds)
  {
    // make sure NULL and INVALID are unique addresses
    bounds_mapt bounds;
    encode_object_bounds(bounds);

    for(postponed_listt::const_iterator it = postponed_list.begin();
        it != postponed_list.end();
        it++)
      do_postponed_typecast(*it, bounds);
  }

  // Clear the list to avoid re-doing in case of incremental usage.
  postponed_list.clear();
}
