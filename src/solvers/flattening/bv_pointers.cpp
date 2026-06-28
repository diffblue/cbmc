/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_pointers.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>

#include <solvers/prop/bdd_expr.h>
#include <solvers/prop/literal_expr.h>

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
  const auto &width_opt = boolbv_width.get_width_opt(src);
  if(!width_opt.has_value())
    return;

  if(src.id() == ID_pointer && boolbv_width.get_pointer_width_multiplier() > 1)
  {
    // Wide pointer encoding: the byte-visible representation is
    // the address component only. Rearrange so that the first
    // platform_width bits come from the address component (which
    // is the last component in [object|offset|address]).
    const std::size_t total = *width_opt;
    const std::size_t platform_width =
      total / boolbv_width.get_pointer_width_multiplier();
    const std::size_t addr_start = total - platform_width;

    const std::size_t base = map.size();
    map.reserve(base + total);

    // First: address bits (byte-visible)
    for(std::size_t i = 0; i < platform_width; ++i)
      map.push_back(base + addr_start + i);
    // Then: object and offset bits (not byte-visible, but must
    // be present to match the bitvector size)
    for(std::size_t i = 0; i < addr_start; ++i)
      map.push_back(base + i);
    return;
  }

  const std::size_t new_size = map.size() + *width_opt;
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

/// Check if a type is an array that (recursively) contains pointer elements.

endianness_mapt
bv_pointerst::endianness_map(const typet &type, bool little_endian) const
{
  if(wide_pointer_encoding)
  {
    const std::size_t bbw = boolbv_width(type);
    const std::size_t bw = bv_width.get_width_opt(type).value_or(0);
    if(bbw != bw)
    {
      endianness_mapt m(ns);
      m.build(unsignedbv_typet{bbw}, little_endian);
      return m;
    }
  }
  return bv_endianness_mapt{type, little_endian, ns, bv_width};
}

std::size_t bv_pointerst::boolbv_width(const typet &type) const
{
  if(!wide_pointer_encoding)
    return bv_width(type);

  // For structs containing pointer arrays, compute recursively
  if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    const auto &st = type.id() == ID_struct_tag
                       ? ns.follow_tag(to_struct_tag_type(type))
                       : to_struct_type(type);
    std::size_t total = 0;
    bool differs = false;
    for(const auto &comp : st.components())
    {
      const std::size_t w = boolbv_width(comp.type());
      total += w;
      if(w != bv_width.get_width_opt(comp.type()).value_or(0))
        differs = true;
    }
    if(differs)
      return total;
  }

  if(type.id() == ID_union || type.id() == ID_union_tag)
  {
    const auto &ut = type.id() == ID_union_tag
                       ? ns.follow_tag(to_union_tag_type(type))
                       : to_union_type(type);
    std::size_t max_w = 0;
    bool differs = false;
    for(const auto &comp : ut.components())
    {
      const std::size_t w = boolbv_width(comp.type());
      max_w = std::max(max_w, w);
      if(w != bv_width.get_width_opt(comp.type()).value_or(0))
        differs = true;
    }
    if(differs)
      return max_w;
  }

  return bv_width(type);
}

std::size_t bv_pointerst::get_object_width(const pointer_typet &type) const
{
  if(wide_pointer_encoding)
    return type.get_width();
  return config.bv_encoding.object_bits;
}

std::size_t bv_pointerst::get_offset_width(const pointer_typet &type) const
{
  if(wide_pointer_encoding)
    return type.get_width();
  const std::size_t pointer_width = type.get_width();
  const std::size_t object_width = get_object_width(type);
  PRECONDITION(pointer_width >= object_width);
  return pointer_width - object_width;
}

std::size_t bv_pointerst::get_address_width(const pointer_typet &type) const
{
  if(wide_pointer_encoding)
    return type.get_width();
  return 0;
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

bvt bv_pointerst::address_literals(const bvt &bv, const pointer_typet &type)
  const
{
  const std::size_t addr_width = get_address_width(type);
  if(addr_width == 0)
    return {};
  const std::size_t offset_width = get_offset_width(type);
  const std::size_t object_width = get_object_width(type);
  const std::size_t start = offset_width + object_width;
  PRECONDITION(bv.size() >= start + addr_width);
  return bvt(bv.begin() + start, bv.begin() + start + addr_width);
}

bvt bv_pointerst::get_object_base_address(
  const mp_integer &object,
  std::size_t width) const
{
  auto it = object_base_address.find(object);
  if(it != object_base_address.end())
    return it->second;
  bvt base = prop.new_variables(width);
  object_base_address[object] = base;
  if(wide_pointer_encoding)
  {
    for(const auto &l : base)
    {
      if(!l.is_constant())
        prop.set_frozen(l);
    }
  }
  return base;
}

bvt bv_pointerst::object_offset_encoding(const bvt &object, const bvt &offset)
{
  bvt result;
  result.reserve(offset.size() + object.size());
  result.insert(result.end(), offset.begin(), offset.end());
  result.insert(result.end(), object.begin(), object.end());

  return result;
}

bvt bv_pointerst::object_offset_encoding(
  const bvt &object,
  const bvt &offset,
  const bvt &address)
{
  bvt result;
  result.reserve(offset.size() + object.size() + address.size());
  result.insert(result.end(), offset.begin(), offset.end());
  result.insert(result.end(), object.begin(), object.end());
  result.insert(result.end(), address.begin(), address.end());

  return result;
}

literalt bv_pointerst::convert_equality(const equal_exprt &expr)
{
  if(wide_pointer_encoding && expr.lhs().type().id() == ID_pointer)
  {
    // Compare pointers by their flat address, not by the full
    // bitvector (which includes object/offset encoding bits).
    // Two pointers are equal iff they point to the same address.
    const bvt &lhs = convert_bv(expr.lhs());
    const bvt &rhs = convert_bv(expr.rhs());
    const auto &type = to_pointer_type(expr.lhs().type());
    bvt lhs_addr = address_literals(lhs, type);
    bvt rhs_addr = address_literals(rhs, type);
    return bv_utils.equal(lhs_addr, rhs_addr);
  }
  return SUB::convert_equality(expr);
}

literalt bv_pointerst::convert_rest(const exprt &expr)
{
  PRECONDITION(expr.is_boolean());

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

      // The comparison is UNSIGNED, to match the type of pointer_offsett
      return prop.land(
        same_object_lit,
        bv_utils.rel(
          offset_bv0,
          expr.id(),
          offset_bv1,
          bv_utilst::representationt::UNSIGNED));
    }
  }
  else if(
    auto prophecy_r_or_w_ok =
      expr_try_dynamic_cast<prophecy_r_or_w_ok_exprt>(expr))
  {
    return convert(simplify_expr(prophecy_r_or_w_ok->lower(ns), ns));
  }
  else if(
    auto prophecy_pointer_in_range =
      expr_try_dynamic_cast<prophecy_pointer_in_range_exprt>(expr))
  {
    return convert(simplify_expr(prophecy_pointer_in_range->lower(ns), ns));
  }

  if(wide_pointer_encoding && expr_try_dynamic_cast<minus_overflow_exprt>(expr))
  {
    const auto &minus_ov = to_binary_overflow_expr(expr);
    if(
      minus_ov.lhs().type().id() == ID_pointer &&
      minus_ov.rhs().type().id() == ID_pointer)
    {
      // For wide pointers, check overflow on the offset bits only,
      // not the full 192-bit bitvector.
      const pointer_typet &pt = to_pointer_type(minus_ov.lhs().type());
      bvt lhs_off = offset_literals(convert_bv(minus_ov.lhs()), pt);
      bvt rhs_off = offset_literals(convert_bv(minus_ov.rhs()), pt);
      return bv_utils.overflow_sub(
        lhs_off, rhs_off, bv_utilst::representationt::SIGNED);
    }
  }

  return SUB::convert_rest(expr);
}

bool bv_pointerst::boolbv_set_equality_to_true(const equal_exprt &expr)
{
  if(
    wide_pointer_encoding && expr.lhs().type().id() == ID_pointer &&
    expr.rhs().type().id() == ID_pointer)
  {
    // Force full bitvector identity (object|offset|address) for an assumed
    // pointer equality, rather than just equating the flat address (as
    // convert_equality does for the *value* of a pointer equality).
    //
    // This is intentionally stronger than address equality: an
    // integer-to-pointer reconstruction assigns fresh, nondeterministic
    // object/offset variables for a given flat address (see
    // reconstruct_pointer_from_address). If `assume(p == q)` only equated the
    // addresses, the solver could still pick *different* object/offset bits for
    // p and q, so a later `*p` and `*q` would read from different objects --
    // a spurious counterexample. Equating all bits ties the two pointers to a
    // single encoding. (Empirically, weakening this to address-only equality
    // reintroduced ~50 spurious VERIFICATION FAILED results across the
    // regression suite.)
    //
    // Trade-off under malloc_may_alias: two distinct objects may share an
    // address after reuse, so this is stronger than the program's `p == q`.
    // It is nonetheless required for the wide encoding to remain consistent
    // with the standard encoding, and is verdict-consistent with it across the
    // regression suite.
    const bvt &lhs_bv = convert_bv(expr.lhs());
    const bvt &rhs_bv = convert_bv(expr.rhs());
    for(std::size_t i = 0; i < lhs_bv.size() && i < rhs_bv.size(); ++i)
      prop.set_equal(lhs_bv[i], rhs_bv[i]);
    return false;
  }
  return SUB::boolbv_set_equality_to_true(expr);
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

std::optional<bvt> bv_pointerst::convert_address_of_rec(const exprt &expr)
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
    auto size = size_of_expr(array_type.element_type(), ns);
    CHECK_RETURN(size.has_value());

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

    // recursive call
    auto bv_opt = convert_address_of_rec(struct_op);
    if(!bv_opt.has_value())
      return {};

    bvt bv = std::move(*bv_opt);
    if(
      struct_op.type().id() == ID_struct ||
      struct_op.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_op_type =
        struct_op.type().id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(struct_op.type()))
          : to_struct_type(struct_op.type());
      auto offset =
        member_offset(struct_op_type, member_expr.get_component_name(), ns);
      CHECK_RETURN(offset.has_value());

      // add offset
      pointer_typet type = pointer_type(expr.type());
      bv = offset_arithmetic(type, bv, *offset);
    }
    else
    {
      INVARIANT(
        struct_op.type().id() == ID_union ||
          struct_op.type().id() == ID_union_tag,
        "member expression should operate on struct or union");
      // nothing to do, all members have offset 0
    }

    return std::move(bv);
  }
  else if(
    expr.is_constant() || expr.id() == ID_string_constant ||
    expr.id() == ID_array)
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

literalt bv_pointerst::i2p_object_eq(pending_i2pt &p, std::size_t number)
{
  if(p.object_eq.size() <= number)
    p.object_eq.resize(number + 1);
  if(!p.object_eq[number].has_value())
  {
    bvt obj_const = bv_utils.build_constant(number, p.obj_bv.size());
    p.object_eq[number] = bv_utils.equal(p.obj_bv, obj_const);
  }
  return *p.object_eq[number];
}

bvt bv_pointerst::reconstruct_pointer_from_address(
  const bvt &addr_bv,
  const pointer_typet &ptr_type,
  bool force_base_for_all_objects)
{
  const std::size_t object_bits = get_object_width(ptr_type);
  const std::size_t offset_bits = get_offset_width(ptr_type);
  const std::size_t addr_bits = get_address_width(ptr_type);

  // Constant 0 => NULL
  if(bv_utils.is_zero(addr_bv).is_true())
    return encode(pointer_logic.get_null_object(), ptr_type);

  bvt obj_bv = prop.new_variables(object_bits);
  bvt off_bv = prop.new_variables(offset_bits);

  // Non-zero address => not null
  bvt null_obj =
    bv_utils.build_constant(pointer_logic.get_null_object(), object_bits);
  prop.l_set_to_true(
    prop.lor(bv_utils.is_zero(addr_bv), !bv_utils.equal(obj_bv, null_obj)));

  // Forward constraints for currently known objects (obj==i =>
  // base[i]+offset==address). Backward constraints, and forward constraints
  // for objects added later, are deferred to finish_eager_conversion.
  const auto &objects = pointer_logic.objects;

  // Create the pending entry up front so the per-object equality literals
  // built below are cached on it and reused by finish_eager_conversion.
  pending_i2p.push_back({obj_bv, off_bv, addr_bv, objects.size(), true, {}});
  pending_i2pt &pending = pending_i2p.back();

  std::size_t number = 0;
  for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
  {
    if(
      !force_base_for_all_objects &&
      object_base_address.find(number) == object_base_address.end())
      continue;
    literalt is_this = i2p_object_eq(pending, number);
    bvt base = get_object_base_address(number, addr_bits);
    bvt off_ext = bv_utils.zero_extension(off_bv, addr_bits);
    bvt flat = bv_utils.add(base, off_ext);
    for(std::size_t k = 0; k < addr_bits; ++k)
    {
      prop.lcnf({!is_this, !flat[k], addr_bv[k]});
      prop.lcnf({!is_this, flat[k], !addr_bv[k]});
    }
  }

  // Freeze the fresh and address variables so MiniSat's simplifier cannot
  // eliminate them: the deferred backward-constraint refinement in
  // finish_eager_conversion / dec_solve reuses them, and an eliminated
  // variable would otherwise trip an invariant.
  for(const auto &l : obj_bv)
    if(!l.is_constant())
      prop.set_frozen(l);
  for(const auto &l : off_bv)
    if(!l.is_constant())
      prop.set_frozen(l);
  for(const auto &l : addr_bv)
    if(!l.is_constant())
      prop.set_frozen(l);

  return object_offset_encoding(obj_bv, off_bv, addr_bv);
}

bvt bv_pointerst::convert_pointer_type(const exprt &expr)
{
  const pointer_typet &type = to_pointer_type(expr.type());

  const std::size_t bits = boolbv_width(expr.type());

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(expr).identifier();

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
      const bvt &op_bv=convert_bv(op);

      if(wide_pointer_encoding)
      {
        // The integer value is the flat address.
        // Reconstruct object and offset using backward constraints.
        const std::size_t addr_bits = get_address_width(type);
        bvt addr_bv = bv_utils.zero_extension(op_bv, addr_bits);

        // Constant 0 => NULL
        if(bv_utils.is_zero(addr_bv).is_true())
          return encode(pointer_logic.get_null_object(), type);

        // Non-zero constant => dedicated integer-address object
        mp_integer int_val = 0;
        bool is_const = true;
        for(std::size_t i = 0; i < addr_bv.size(); ++i)
        {
          if(addr_bv[i].is_true())
            int_val += power(2, i);
          else if(!addr_bv[i].is_false())
          {
            is_const = false;
            break;
          }
        }
        if(is_const)
        {
          const auto int_addr_obj = pointer_logic.add_object(constant_exprt(
            integer2bvrep(int_val, addr_bits), unsignedbv_typet(addr_bits)));
          bvt result = encode(int_addr_obj, type);
          integer_address_objects.insert(int_addr_obj);
          // Set the base address to the constant value
          bvt base = get_object_base_address(int_addr_obj, addr_bits);
          bvt val_bv = bv_utils.build_constant(int_val, addr_bits);
          for(std::size_t i = 0; i < addr_bits; ++i)
            prop.set_equal(base[i], val_bv[i]);
          return result;
        }

        return reconstruct_pointer_from_address(addr_bv, type, true);
      }

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
  else if(expr.id() == ID_object_address)
  {
    const auto &object_address_expr = to_object_address_expr(expr);
    return add_addr(object_address_expr.object_expr());
  }
  else if(expr.is_constant())
  {
    const constant_exprt &c = to_constant_expr(expr);

    if(c.is_null_pointer())
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

    for(const auto &op : plus_expr.operands())
    {
      if(op.type().id() == ID_pointer)
      {
        count++;
        bv = convert_bv(op);
        CHECK_RETURN(bv.size()==bits);

        typet pointer_base_type = to_pointer_type(op.type()).base_type();
        DATA_INVARIANT(
          pointer_base_type.id() != ID_empty,
          "no pointer arithmetic over void pointers");
        auto size_opt = pointer_offset_size(pointer_base_type, ns);
        CHECK_RETURN(size_opt.has_value() && *size_opt >= 0);
        size = *size_opt;
      }
    }

    INVARIANT(
      count == 1,
      "there should be exactly one pointer-type operand in a pointer-type sum");

    const std::size_t offset_bits = get_offset_width(type);
    bvt sum = bv_utils.build_constant(0, offset_bits);

    for(const auto &operand : plus_expr.operands())
    {
      if(operand.type().id() == ID_pointer)
        continue;

      if(
        operand.type().id() != ID_unsignedbv &&
        operand.type().id() != ID_signedbv)
      {
        return conversion_failed(plus_expr);
      }

      bv_utilst::representationt rep = operand.type().id() == ID_signedbv
                                         ? bv_utilst::representationt::SIGNED
                                         : bv_utilst::representationt::UNSIGNED;

      bvt op = convert_bv(operand);
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
    DATA_INVARIANT(
      pointer_base_type.id() != ID_empty,
      "no pointer arithmetic over void pointers");
    auto element_size_opt = pointer_offset_size(pointer_base_type, ns);
    CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
    return offset_arithmetic(type, bv, *element_size_opt, neg_op1);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    return convert_byte_extract(to_byte_extract_expr(expr));
  }
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    return convert_byte_update(to_byte_update_expr(expr));
  }
  else if(expr.id() == ID_field_address)
  {
    const auto &field_address_expr = to_field_address_expr(expr);
    const typet &compound_type = field_address_expr.compound_type();

    // recursive call
    auto bv = convert_bitvector(field_address_expr.base());

    if(compound_type.id() == ID_struct || compound_type.id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        compound_type.id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(compound_type))
          : to_struct_type(compound_type);
      auto offset =
        member_offset(struct_type, field_address_expr.component_name(), ns);
      CHECK_RETURN(offset.has_value());

      // add offset
      bv = offset_arithmetic(field_address_expr.type(), bv, *offset);
    }
    else if(
      compound_type.id() == ID_union || compound_type.id() == ID_union_tag)
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

bvt bv_pointerst::convert_byte_extract(const byte_extract_exprt &expr)
{
  if(!wide_pointer_encoding)
    return SUB::convert_byte_extract(expr);

  if(expr.op().type().id() == ID_pointer)
  {
    const auto &ptr_type = to_pointer_type(expr.op().type());
    const std::size_t pw = ptr_type.get_width();
    byte_extract_exprt addr_extract(
      expr.id(),
      typecast_exprt(expr.op(), unsignedbv_typet{pw}),
      expr.offset(),
      expr.get_bits_per_byte(),
      expr.type());
    return SUB::convert_byte_extract(addr_extract);
  }

  // Source is a pointer array: extract addresses, byte_extract from those
  if(
    expr.op().type().id() == ID_array &&
    to_array_type(expr.op().type()).element_type().id() == ID_pointer &&
    expr.type().id() == ID_pointer)
  {
    const auto &arr_type = to_array_type(expr.op().type());
    const auto &ptr_type = to_pointer_type(arr_type.element_type());
    const std::size_t pw = ptr_type.get_width();
    const auto sz = numeric_cast<mp_integer>(arr_type.size());

    if(sz.has_value() && *sz > 0)
    {
      const bvt &arr_bv = convert_bv(expr.op());
      const std::size_t enc_w = boolbv_width(ptr_type);

      // Extract address (last pw bits) from each element
      bvt addr_arr;
      for(mp_integer i = 0; i < *sz; ++i)
      {
        std::size_t base = numeric_cast_v<std::size_t>(i * enc_w);
        std::size_t addr_start = base + enc_w - pw;
        for(std::size_t j = 0; j < pw; ++j)
          addr_arr.push_back(arr_bv[addr_start + j]);
      }

      // Byte_extract from the address array
      const std::size_t bpb = expr.get_bits_per_byte();
      bvt addr_result(pw, const_literal(false));

      const auto off_opt = numeric_cast<mp_integer>(expr.offset());
      if(off_opt.has_value())
      {
        std::size_t bit_off = numeric_cast_v<std::size_t>(*off_opt * bpb);
        if(bit_off + pw <= addr_arr.size())
          addr_result =
            bvt(addr_arr.begin() + bit_off, addr_arr.begin() + bit_off + pw);
      }
      else
      {
        for(std::size_t off = 0; off + pw <= addr_arr.size(); off += bpb)
        {
          literalt is_off = convert(equal_exprt(
            expr.offset(), from_integer(off / bpb, expr.offset().type())));
          for(std::size_t j = 0; j < pw; ++j)
            addr_result[j] =
              prop.lselect(is_off, addr_arr[off + j], addr_result[j]);
        }
      }

      // Reconstruct pointer from address
      return reconstruct_pointer_from_address(addr_result, ptr_type, false);
    }
  }

  if(expr.type().id() != ID_pointer)
    return SUB::convert_byte_extract(expr);

  // Extract only the platform-width address from the byte array,
  // then reconstruct the full wide pointer encoding.
  const auto &ptr_type = to_pointer_type(expr.type());
  const std::size_t platform_width = ptr_type.get_width();

  // Create a byte_extract that returns an unsigned integer of
  // platform width (the flat address)
  byte_extract_exprt addr_extract(
    expr.id(),
    expr.op(),
    expr.offset(),
    expr.get_bits_per_byte(),
    unsignedbv_typet{platform_width});
  bvt addr_bv = SUB::convert_byte_extract(addr_extract);

  // Reconstruct the full pointer from the flat address (same logic as I2P).
  return reconstruct_pointer_from_address(addr_bv, ptr_type, false);
}

bvt bv_pointerst::convert_byte_update(const byte_update_exprt &expr)
{
  if(!wide_pointer_encoding)
    return SUB::convert_byte_update(expr);

  // Target is a pointer: update only the address component
  if(expr.op().type().id() == ID_pointer)
  {
    const auto &ptr_type = to_pointer_type(expr.op().type());
    const std::size_t pw = ptr_type.get_width();
    bvt ptr_bv = convert_bv(expr.op());
    byte_update_exprt addr_update(
      expr.id(),
      typecast_exprt(expr.op(), unsignedbv_typet{pw}),
      expr.offset(),
      expr.value(),
      expr.get_bits_per_byte());
    bvt new_addr = SUB::convert_byte_update(addr_update);
    bvt obj = object_literals(ptr_bv, ptr_type);
    bvt off = offset_literals(ptr_bv, ptr_type);
    return object_offset_encoding(obj, off, new_addr);
  }

  // Value is a pointer: write only the address
  if(expr.value().type().id() == ID_pointer)
  {
    const auto &ptr_type = to_pointer_type(expr.value().type());
    const std::size_t platform_width = ptr_type.get_width();

    // Extract the address component from the pointer value
    const bvt &value_bv = convert_bv(expr.value());
    bvt addr_bv = address_literals(value_bv, ptr_type);

    // Create a byte_update that writes the address as an unsigned integer
    // We need to create a fresh symbol for the address value
    // and use it in a byte_update with the integer type.
    // Simpler: lower to byte_update with the address as a typecast.
    const typecast_exprt addr_as_int(
      expr.value(), unsignedbv_typet{platform_width});
    byte_update_exprt int_update(
      expr.id(),
      expr.op(),
      expr.offset(),
      addr_as_int,
      expr.get_bits_per_byte());
    return SUB::convert_byte_update(int_update);
  }

  // For compound types containing pointers: lower to individual
  // byte operations (let the default lowering handle it)
  return convert_bv(lower_byte_update(expr, ns));
}

bvt bv_pointerst::convert_bitvector(const exprt &expr)
{
  if(expr.type().id()==ID_pointer)
    return convert_pointer_type(expr);

  if(is_pointer_subtraction(expr))
  {
    std::size_t width=boolbv_width(expr.type());

    // pointer minus pointer is subtraction over the offset divided by element
    // size, iff the pointers point to the same object
    const auto &minus_expr = to_minus_expr(expr);

    // do the same-object-test via an expression as this may permit re-using
    // already cached encodings of the equality test
    const exprt same_object = ::same_object(minus_expr.lhs(), minus_expr.rhs());
    const literalt same_object_lit = convert(same_object);

    bvt bv = prop.new_variables(width);

    if(!same_object_lit.is_false())
    {
      const pointer_typet &lhs_pt = to_pointer_type(minus_expr.lhs().type());
      const bvt &lhs = convert_bv(minus_expr.lhs());
      const bvt lhs_offset =
        bv_utils.zero_extension(offset_literals(lhs, lhs_pt), width);

      const pointer_typet &rhs_pt = to_pointer_type(minus_expr.rhs().type());
      const bvt &rhs = convert_bv(minus_expr.rhs());
      const bvt rhs_offset =
        bv_utils.zero_extension(offset_literals(rhs, rhs_pt), width);

      bvt difference = bv_utils.sub(lhs_offset, rhs_offset);

      DATA_INVARIANT(
        lhs_pt.base_type().id() != ID_empty,
        "no pointer arithmetic over void pointers");
      auto element_size_opt = pointer_offset_size(lhs_pt.base_type(), ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);

      if(*element_size_opt != 1)
      {
        bvt element_size_bv = bv_utils.build_constant(*element_size_opt, width);
        difference = bv_utils.divider(
          difference, element_size_bv, bv_utilst::representationt::SIGNED);
      }

      prop.l_set_to_true(
        prop.limplies(same_object_lit, bv_utils.equal(difference, bv)));
    }

    // Wide encoding: different objects => use address difference
    if(wide_pointer_encoding && !same_object_lit.is_true())
    {
      const pointer_typet &lhs_pt = to_pointer_type(minus_expr.lhs().type());
      const bvt &lhs = convert_bv(minus_expr.lhs());
      bvt lhs_addr =
        bv_utils.zero_extension(address_literals(lhs, lhs_pt), width);

      const pointer_typet &rhs_pt = to_pointer_type(minus_expr.rhs().type());
      const bvt &rhs = convert_bv(minus_expr.rhs());
      bvt rhs_addr =
        bv_utils.zero_extension(address_literals(rhs, rhs_pt), width);

      bvt addr_diff = bv_utils.sub(lhs_addr, rhs_addr);

      auto element_size_opt = pointer_offset_size(lhs_pt.base_type(), ns);
      CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
      if(*element_size_opt != 1)
      {
        bvt element_size_bv = bv_utils.build_constant(*element_size_opt, width);
        addr_diff = bv_utils.divider(
          addr_diff, element_size_bv, bv_utilst::representationt::SIGNED);
      }

      prop.l_set_to_true(
        prop.limplies(!same_object_lit, bv_utils.equal(addr_diff, bv)));
    }

    return bv;
  }
  else if(
    expr.id() == ID_pointer_offset &&
    to_pointer_offset_expr(expr).pointer().type().id() == ID_pointer)
  {
    std::size_t width=boolbv_width(expr.type());

    const exprt &pointer = to_pointer_offset_expr(expr).pointer();
    const bvt &pointer_bv = convert_bv(pointer);

    bvt offset_bv =
      offset_literals(pointer_bv, to_pointer_type(pointer.type()));

    return bv_utils.zero_extension(offset_bv, width);
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
  else if(wide_pointer_encoding && expr.id() == ID_object_base_address)
  {
    // Postpone until all objects are known.
    std::size_t width = boolbv_width(expr.type());

    const auto &ptr = to_object_base_address_expr(expr).pointer();
    postponed_list.emplace_back(
      prop.new_variables(width), convert_bv(ptr), expr);

    return postponed_list.back().bv;
  }
  else if(
    expr.id() == ID_pointer_object &&
    to_pointer_object_expr(expr).pointer().type().id() == ID_pointer)
  {
    std::size_t width=boolbv_width(expr.type());

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
    bvt op0 = convert_bv(to_typecast_expr(expr).op());

    std::size_t width=boolbv_width(expr.type());

    if(wide_pointer_encoding)
    {
      // Return the flat integer address.
      const auto &ptr_type =
        to_pointer_type(to_typecast_expr(expr).op().type());
      bvt addr = address_literals(op0, ptr_type);
      return bv_utils.zero_extension(addr, width);
    }

    // squeeze it in!
    return bv_utils.zero_extension(op0, width);
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
  std::size_t offset) const
{
  const typet &type = expr.type();

  if(type.id() != ID_pointer)
    return SUB::bv_get_rec(expr, bv, offset);

  const pointer_typet &pt = to_pointer_type(type);
  const std::size_t bits = boolbv_width(pt);
  bvt value_bv(bv.begin() + offset, bv.begin() + offset + bits);

  std::string value = bits_to_string(prop, value_bv);
  std::string value_addr = bits_to_string(prop, object_literals(value_bv, pt));
  std::string value_offset =
    bits_to_string(prop, offset_literals(value_bv, pt));

  // we treat these like bit-vector constants, but with
  // some additional annotation

  const irep_idt bvrep = [&]()
  {
    if(wide_pointer_encoding)
    {
      // For trace output, use the address component (platform width)
      bvt addr_bv = address_literals(value_bv, pt);
      std::string addr_str = bits_to_string(prop, addr_bv);
      const std::size_t pw = pt.get_width();
      return make_bvrep(
        pw,
        [&addr_str](std::size_t i)
        { return addr_str[addr_str.size() - 1 - i] == '1'; });
    }
    return make_bvrep(
      bits,
      [&value](std::size_t i) { return value[value.size() - 1 - i] == '1'; });
  }();

  constant_exprt result(bvrep, type);

  pointer_logict::pointert pointer{
    numeric_cast_v<std::size_t>(binary2integer(value_addr, false)),
    binary2integer(value_offset, false)};

  return annotated_pointer_constant_exprt{
    bvrep, pointer_logic.pointer_expr(pointer, pt)};
}

bvt bv_pointerst::encode(const mp_integer &addr, const pointer_typet &type)
  const
{
  const std::size_t offset_bits = get_offset_width(type);
  const std::size_t object_bits = get_object_width(type);

  bvt zero_offset(offset_bits, const_literal(false));
  bvt object = bv_utils.build_constant(addr, object_bits);

  if(wide_pointer_encoding)
  {
    const std::size_t addr_bits = get_address_width(type);
    bvt base = get_object_base_address(addr, addr_bits);
    return object_offset_encoding(object, zero_offset, base);
  }

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
  const exprt &factor,
  const exprt &index)
{
  bvt bv_factor = convert_bv(factor);
  bvt bv_index =
    convert_bv(typecast_exprt::conditional_cast(index, factor.type()));

  bv_utilst::representationt rep = factor.type().id() == ID_signedbv
                                     ? bv_utilst::representationt::SIGNED
                                     : bv_utilst::representationt::UNSIGNED;

  bv_index = bv_utils.multiplier(bv_index, bv_factor, rep);

  const std::size_t offset_bits = get_offset_width(type);
  bv_index = bv_utils.extension(bv_index, offset_bits, rep);

  return offset_arithmetic(type, bv, 1, bv_index);
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
  bv_index = bv_utils.zero_extension(bv_index, offset_bits);

  bvt offset_bv = offset_literals(bv, type);

  bvt bv_tmp = bv_utils.add(offset_bv, bv_index);

  if(wide_pointer_encoding)
  {
    // Also update the address component
    bvt addr = address_literals(bv, type);
    bvt addr_index = bv_utils.sign_extension(bv_index, addr.size());
    bvt new_addr = bv_utils.add(addr, addr_index);
    return object_offset_encoding(object_literals(bv, type), bv_tmp, new_addr);
  }

  return object_offset_encoding(object_literals(bv, type), bv_tmp);
}

bvt bv_pointerst::add_addr(const exprt &expr)
{
  const auto a = pointer_logic.add_object(expr);

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

std::pair<exprt, exprt> bv_pointerst::prepare_postponed_is_dynamic_object(
  std::vector<symbol_exprt> &placeholders) const
{
  PRECONDITION(placeholders.empty());

  const auto &objects = pointer_logic.objects;
  std::size_t number = 0;

  exprt::operandst dynamic_objects_ops, not_dynamic_objects_ops;
  dynamic_objects_ops.reserve(objects.size());
  not_dynamic_objects_ops.reserve(objects.size());

  for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
  {
    const exprt &expr = *it;

    // only compare object part
    pointer_typet pt = pointer_type(expr.type());
    bvt bv = object_literals(encode(number, pt), pt);

    exprt::operandst conjuncts;
    conjuncts.reserve(bv.size());
    placeholders.reserve(bv.size());
    for(std::size_t i = 0; i < bv.size(); ++i)
    {
      if(placeholders.size() <= i)
        placeholders.push_back(symbol_exprt{std::to_string(i), bool_typet{}});

      POSTCONDITION(bv[i].is_constant());
      if(bv[i].is_true())
        conjuncts.emplace_back(placeholders[i]);
      else
        conjuncts.emplace_back(not_exprt{placeholders[i]});
    }

    if(pointer_logic.is_dynamic_object(expr))
      dynamic_objects_ops.push_back(conjunction(conjuncts));
    else
      not_dynamic_objects_ops.push_back(conjunction(conjuncts));
  }

  exprt dynamic_objects = disjunction(dynamic_objects_ops);
  exprt not_dynamic_objects = disjunction(not_dynamic_objects_ops);

  bdd_exprt bdd_converter;
  bddt dyn_bdd = bdd_converter.from_expr(dynamic_objects);
  bddt not_dyn_bdd = bdd_converter.from_expr(not_dynamic_objects);

  return {bdd_converter.as_expr(dyn_bdd), bdd_converter.as_expr(not_dyn_bdd)};
}

std::unordered_map<exprt, exprt, irep_hash>
bv_pointerst::prepare_postponed_object_size(
  std::vector<symbol_exprt> &placeholders) const
{
  PRECONDITION(placeholders.empty());

  const auto &objects = pointer_logic.objects;
  std::size_t number = 0;

  std::unordered_map<exprt, exprt::operandst, irep_hash> per_size_object_ops;

  for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
  {
    const exprt &expr = *it;

    if(expr.id() != ID_symbol && expr.id() != ID_string_constant)
      continue;

    const auto size_expr = size_of_expr(expr.type(), ns);
    if(!size_expr.has_value())
      continue;

    // only compare object part
    pointer_typet pt = pointer_type(expr.type());
    bvt bv = object_literals(encode(number, pt), pt);

    exprt::operandst conjuncts;
    conjuncts.reserve(bv.size());
    placeholders.reserve(bv.size());
    for(std::size_t i = 0; i < bv.size(); ++i)
    {
      if(placeholders.size() <= i)
        placeholders.push_back(symbol_exprt{std::to_string(i), bool_typet{}});

      POSTCONDITION(bv[i].is_constant());
      if(bv[i].is_true())
        conjuncts.emplace_back(placeholders[i]);
      else
        conjuncts.emplace_back(not_exprt{placeholders[i]});
    }

    per_size_object_ops[size_expr.value()].push_back(conjunction(conjuncts));
  }

  std::unordered_map<exprt, exprt, irep_hash> result;
  for(const auto &size_entry : per_size_object_ops)
  {
    exprt all_objects_this_size = disjunction(size_entry.second);
    bdd_exprt bdd_converter;
    bddt bdd = bdd_converter.from_expr(all_objects_this_size);

    result.emplace(size_entry.first, bdd_converter.as_expr(bdd));
  }

  return result;
}

void bv_pointerst::finish_eager_conversion()
{
  // post-processing arrays may yield further objects, do this first
  SUB::finish_eager_conversion();

  // Performance note: under the wide encoding this post-processing is the main
  // source of the back-end overhead (symbolic execution itself is unaffected by
  // the encoding). It runs several passes that are O(#objects) -- the
  // is_dynamic_object / object_size BDD encodings (prepare_postponed_*) and the
  // object_base_address MUX -- plus one that is O(#pending I2P casts x
  // #objects): the deferred integer-to-pointer address constraints below.
  // Together with the 3x-wider (192-bit) pointer bitvectors this grows the SAT
  // instance roughly linearly in the number of pointer objects, so the cost is
  // concentrated in pointer-heavy programs while pointer-light ones see
  // essentially no overhead.

  // it would seem nicer to use `optionalt` here, but GCC >= 12 produces
  // spurious warnings about accessing uninitialized objects
  std::pair<exprt, exprt> is_dynamic_expr = {nil_exprt{}, nil_exprt{}};
  std::vector<symbol_exprt> is_dynamic_placeholders;

  std::unordered_map<exprt, exprt, irep_hash> object_sizes;
  std::vector<symbol_exprt> object_size_placeholders;

  for(const postponedt &postponed : postponed_list)
  {
    if(postponed.expr.id() == ID_is_dynamic_object)
    {
      if(is_dynamic_expr.first.is_nil())
        is_dynamic_expr =
          prepare_postponed_is_dynamic_object(is_dynamic_placeholders);

      const auto &type =
        to_pointer_type(to_unary_expr(postponed.expr).op().type());
      bvt saved_bv = object_literals(postponed.op, type);
      POSTCONDITION(saved_bv.size() == is_dynamic_placeholders.size());
      replace_mapt replacements;
      for(std::size_t i = 0; i < saved_bv.size(); ++i)
      {
        replacements.emplace(
          is_dynamic_placeholders[i], literal_exprt{saved_bv[i]});
      }
      exprt is_dyn = is_dynamic_expr.first;
      replace_expr(replacements, is_dyn);
      exprt is_not_dyn = is_dynamic_expr.second;
      replace_expr(replacements, is_not_dyn);

      PRECONDITION(postponed.bv.size() == 1);
      prop.l_set_to_true(
        prop.limplies(convert_bv(is_dyn)[0], postponed.bv.front()));
      prop.l_set_to_true(
        prop.limplies(convert_bv(is_not_dyn)[0], !postponed.bv.front()));
    }
    else if(
      const auto postponed_object_size =
        expr_try_dynamic_cast<object_size_exprt>(postponed.expr))
    {
      if(object_sizes.empty())
        object_sizes = prepare_postponed_object_size(object_size_placeholders);

      // we might not have any usable objects
      if(object_size_placeholders.empty())
        continue;

      const auto &type =
        to_pointer_type(postponed_object_size->pointer().type());
      bvt saved_bv = object_literals(postponed.op, type);
      POSTCONDITION(saved_bv.size() == object_size_placeholders.size());
      replace_mapt replacements;
      for(std::size_t i = 0; i < saved_bv.size(); ++i)
      {
        replacements.emplace(
          object_size_placeholders[i], literal_exprt{saved_bv[i]});
      }

      for(const auto &object_size_entry : object_sizes)
      {
        const exprt object_size = typecast_exprt::conditional_cast(
          object_size_entry.first, postponed_object_size->type());
        bvt size_bv = convert_bv(object_size);
        POSTCONDITION(size_bv.size() == postponed.bv.size());

        exprt all_objects_this_size = object_size_entry.second;
        replace_expr(replacements, all_objects_this_size);

        literalt l1 = convert_bv(all_objects_this_size)[0];
        if(l1.is_true())
        {
          for(std::size_t i = 0; i < postponed.bv.size(); ++i)
            prop.set_equal(postponed.bv[i], size_bv[i]);
          break;
        }
        else if(l1.is_false())
          continue;
#define COMPACT_OBJECT_SIZE_EQ
#ifndef COMPACT_OBJECT_SIZE_EQ
        literalt l2 = bv_utils.equal(postponed.bv, size_bv);

        prop.l_set_to_true(prop.limplies(l1, l2));
#else
        for(std::size_t i = 0; i < postponed.bv.size(); ++i)
        {
          prop.lcnf({!l1, !postponed.bv[i], size_bv[i]});
          prop.lcnf({!l1, postponed.bv[i], !size_bv[i]});
        }
#endif
      }
    }
    else if(postponed.expr.id() == ID_object_base_address)
    {
      // MUX: for each object i, if pointer_object(ptr)==i then base[i]
      const auto &ptr_type = to_pointer_type(
        to_object_base_address_expr(postponed.expr).pointer().type());
      bvt obj_bv = object_literals(postponed.op, ptr_type);
      const std::size_t addr_width = postponed.bv.size();

      const auto &objects = pointer_logic.objects;
      std::size_t number = 0;
      for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
      {
        bvt obj_const = bv_utils.build_constant(number, obj_bv.size());
        literalt is_this = bv_utils.equal(obj_bv, obj_const);
        bvt base = get_object_base_address(number, addr_width);
        for(std::size_t k = 0; k < addr_width; ++k)
        {
          prop.lcnf({!is_this, !base[k], postponed.bv[k]});
          prop.lcnf({!is_this, base[k], !postponed.bv[k]});
        }
      }
    }
    else
      UNREACHABLE;
  }

  // Clear the list to avoid re-doing in case of incremental usage.
  postponed_list.clear();

  // Record variable count before adding wide encoding constraints
  if(wide_pointer_encoding)
    finish_eager_var_start = prop.no_variables();

  // Add deferred I2P constraints now that all objects are known
  if(wide_pointer_encoding)
  {
    const auto &objects = pointer_logic.objects;
    for(auto &p : pending_i2p)
    {
      const std::size_t addr_bits = p.addr_bv.size();

      std::vector<literalt> valid_obj_lits;
      std::size_t number = 0;
      for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
      {
        literalt is_this = i2p_object_eq(p, number);
        valid_obj_lits.push_back(is_this);

        // Forward constraints for objects added after the I2P
        if(number >= p.objects_at_creation)
        {
          bvt base = get_object_base_address(number, addr_bits);
          bvt off_ext = bv_utils.zero_extension(p.off_bv, addr_bits);
          bvt flat = bv_utils.add(base, off_ext);
          for(std::size_t k = 0; k < addr_bits; ++k)
          {
            prop.lcnf({!is_this, !flat[k], p.addr_bv[k]});
            prop.lcnf({!is_this, flat[k], !p.addr_bv[k]});
          }
        }
      }
      if(!valid_obj_lits.empty())
        prop.lcnf(valid_obj_lits);
    }
  }

  // Add non-overlapping constraints for wide pointer base addresses
  if(wide_pointer_encoding && !object_base_address.empty())
  {
    const std::size_t addr_width = config.ansi_c.pointer_width;

    // NULL base address = 0
    bvt null_base =
      get_object_base_address(pointer_logic.get_null_object(), addr_width);
    bvt zero_bv = bv_utils.build_constant(0, addr_width);
    for(std::size_t i = 0; i < addr_width; ++i)
      prop.set_equal(null_base[i], zero_bv[i]);

    // Collect objects with base addresses and known sizes
    const auto &objects = pointer_logic.objects;
    struct obj_infot
    {
      mp_integer number;
      mp_integer size;
      bool is_dynamic;
    };
    std::vector<obj_infot> obj_infos;
    std::size_t number = 0;
    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
    {
      if(object_base_address.find(number) == object_base_address.end())
        continue;
      // Skip integer-address objects — their addresses may
      // overlap with regular objects.
      if(integer_address_objects.count(number))
        continue;
      auto size_opt = pointer_offset_size(it->type(), ns);
      mp_integer size =
        (size_opt.has_value() && *size_opt > 0) ? *size_opt : mp_integer{1};
      obj_infos.push_back(
        {mp_integer(number), size, pointer_logic.is_dynamic_object(*it)});

      // Overflow guard: base + size must not overflow
      bvt base = get_object_base_address(mp_integer(number), addr_width);
      bvt end = bv_utils.add(base, bv_utils.build_constant(size, addr_width));
      // end >= base (no wrap-around)
      prop.l_set_to_true(
        bv_utils.rel(end, ID_ge, base, bv_utilst::representationt::UNSIGNED));
      // Object base addresses are aligned, mirroring CBMC's standard pointer
      // model (which also assumes objects are aligned -- e.g. the address of
      // an `int` has its low bits zero). This keeps the flat addresses of the
      // wide encoding consistent with the standard encoding; without it,
      // programs that observe object alignment (e.g. regression test Pointer2,
      // which asserts `((size_t)&x & 1) == 0`) would diverge from standard
      // mode. We align to the largest power of two not exceeding the object
      // size (capped at the address word size); this is a conservative
      // approximation of the object's true alignment that is never weaker than
      // what the standard model assumes.
      mp_integer alignment = std::min(size, mp_integer(addr_width / 8));
      mp_integer align_pow2 = 1;
      while(align_pow2 * 2 <= alignment)
        align_pow2 *= 2;
      if(align_pow2 > 1)
      {
        std::size_t align_bits = 0;
        mp_integer tmp = align_pow2;
        while(tmp > 1)
        {
          align_bits++;
          tmp /= 2;
        }
        for(std::size_t i = 0; i < align_bits && i < addr_width; ++i)
          prop.l_set_to_true(!base[i]);
      }
    }

    // Non-overlapping: chain constraint (O(n) instead of O(n²))
    // Objects are ordered by index: base[0]+size[0] <= base[1], etc.
    for(std::size_t i = 0; i + 1 < obj_infos.size(); ++i)
    {
      bvt base_i = get_object_base_address(obj_infos[i].number, addr_width);
      bvt end_i = bv_utils.add(
        base_i, bv_utils.build_constant(obj_infos[i].size, addr_width));
      bvt base_next =
        get_object_base_address(obj_infos[i + 1].number, addr_width);

      prop.l_set_to_true(bv_utils.rel(
        end_i, ID_le, base_next, bv_utilst::representationt::UNSIGNED));
    }
  }
  // Freeze variables created during finish_eager_conversion
  // (non-overlapping constraints, deferred I2P forward constraints)
  // to prevent MiniSat's simplifier from eliminating them.
  // The backward constraint refinement in dec_solve creates
  // bv_utils operations that may reuse these variables.
  if(wide_pointer_encoding && finish_eager_var_start > 0)
  {
    for(unsigned i = finish_eager_var_start; i < prop.no_variables(); ++i)
      prop.set_frozen(literalt(i, false));
  }
}

bool bv_pointerst::check_SAT_backward_i2p()
{
  const auto &objects = pointer_logic.objects;
  bool any_violation = false;

  for(const auto &p : pending_i2p)
  {
    if(!p.needs_backward_constraints)
      continue;
    if(any_violation)
      break;

    const std::size_t object_bits = p.obj_bv.size();
    const std::size_t addr_bits = p.addr_bv.size();

    mp_integer obj_val = 0;
    for(std::size_t i = 0; i < object_bits; ++i)
      if(prop.l_get(p.obj_bv[i]).is_true())
        obj_val += power(2, i);

    mp_integer addr_val = 0;
    for(std::size_t i = 0; i < addr_bits; ++i)
      if(prop.l_get(p.addr_bv[i]).is_true())
        addr_val += power(2, i);

    std::size_t number = 0;
    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
    {
      if(object_base_address.find(number) == object_base_address.end())
        continue;
      auto sz = pointer_offset_size(it->type(), ns);
      if(!sz.has_value() || *sz <= 0)
        continue;
      bvt base = get_object_base_address(number, addr_bits);
      mp_integer base_val = 0;
      for(std::size_t i = 0; i < addr_bits; ++i)
        if(prop.l_get(base[i]).is_true())
          base_val += power(2, i);
      if(
        addr_val >= base_val && addr_val < base_val + *sz &&
        obj_val != mp_integer(number))
      {
        any_violation = true;
        break;
      }
    }
  }

  if(!any_violation)
    return false;

  // A spurious non-overlapping model was found. Add the deferred backward I2P
  // constraints (address within an object's range implies that object's id)
  // for the affected integer-to-pointer reconstructions so the next solve
  // cannot reproduce it, then request a re-solve below.

  for(auto &p : pending_i2p)
  {
    if(!p.needs_backward_constraints)
      continue;
    const std::size_t a_bits = p.addr_bv.size();
    std::size_t num = 0;
    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++num)
    {
      if(object_base_address.find(num) == object_base_address.end())
        continue;
      auto sz = pointer_offset_size(it->type(), ns);
      if(!sz.has_value() || *sz <= 0)
        continue;
      bvt base = get_object_base_address(num, a_bits);
      literalt is_this = i2p_object_eq(p, num);
      literalt ge = bv_utils.rel(
        p.addr_bv, ID_ge, base, bv_utilst::representationt::UNSIGNED);
      bvt end_bv = bv_utils.add(base, bv_utils.build_constant(*sz, a_bits));
      literalt lt = bv_utils.rel(
        p.addr_bv, ID_lt, end_bv, bv_utilst::representationt::UNSIGNED);
      prop.l_set_to_true(prop.limplies(prop.land(ge, lt), is_this));
    }
  }
  for(auto &p : pending_i2p)
    p.needs_backward_constraints = false;
  return true;
}

decision_proceduret::resultt bv_pointerst::dec_solve(const exprt &assumption)
{
  if(!wide_pointer_encoding)
    return SUB::dec_solve(assumption);

  while(true)
  {
    auto result = SUB::dec_solve(assumption);
    if(result != resultt::D_SATISFIABLE)
      return result;
    if(!check_SAT_backward_i2p())
      return result;
  }
}
