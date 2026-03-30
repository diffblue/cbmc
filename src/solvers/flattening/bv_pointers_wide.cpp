/*******************************************************************\

Module:

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Pointer encoding using solver-level maps (arrays)

#include "bv_pointers_wide.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
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
class bv_endianness_map_widet : public endianness_mapt
{
public:
  bv_endianness_map_widet(
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

void bv_endianness_map_widet::build_little_endian(const typet &src)
{
  const auto &width_opt = boolbv_width.get_width_opt(src);
  if(!width_opt.has_value())
    return;

  const std::size_t new_size = map.size() + *width_opt;
  map.reserve(new_size);

  for(std::size_t i = map.size(); i < new_size; ++i)
    map.push_back(i);
}

void bv_endianness_map_widet::build_big_endian(const typet &src)
{
  if(src.id() == ID_pointer)
    build_little_endian(src);
  else
    endianness_mapt::build_big_endian(src);
}

endianness_mapt
bv_pointers_widet::endianness_map(const typet &type, bool little_endian) const
{
  return bv_endianness_map_widet{type, little_endian, ns, bv_width};
}

// Width helpers -- in the map-based encoding every component uses
// the full pointer width.

std::size_t bv_pointers_widet::get_object_width(const pointer_typet &type) const
{
  return type.get_width();
}

std::size_t bv_pointers_widet::get_offset_width(const pointer_typet &type) const
{
  return type.get_width();
}

std::size_t
bv_pointers_widet::get_address_width(const pointer_typet &type) const
{
  return type.get_width();
}

// Constructor

bv_pointers_widet::bv_pointers_widet(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &message_handler,
  bool get_array_constraints)
  : boolbvt(_ns, _prop, message_handler, get_array_constraints),
    pointer_logic(_ns),
    object_map(
      "bv_pointers_wide::object_map",
      array_typet(
        unsignedbv_typet(config.ansi_c.pointer_width),
        infinity_exprt(unsignedbv_typet(config.ansi_c.pointer_width)))),
    offset_map(
      "bv_pointers_wide::offset_map",
      array_typet(
        unsignedbv_typet(config.ansi_c.pointer_width),
        infinity_exprt(unsignedbv_typet(config.ansi_c.pointer_width)))),
    base_address_map(
      "bv_pointers_wide::base_address_map",
      array_typet(
        unsignedbv_typet(config.ansi_c.pointer_width),
        infinity_exprt(unsignedbv_typet(config.ansi_c.pointer_width)))),
    next_bv_pointer_index(0)
{
}

// Helper: build a constant expression from a pointer index.

exprt bv_pointers_widet::index_to_expr(
  const mp_integer &index,
  const pointer_typet &type) const
{
  return from_integer(index, unsignedbv_typet(type.get_width()));
}

// Read helpers: look up object/offset via solver-level arrays.

bvt bv_pointers_widet::read_object(const bvt &bv, const pointer_typet &type)
{
  // Try direct lookup from the index to avoid array reads
  mp_integer idx_val = 0;
  bool is_const = true;
  for(std::size_t i = 0; i < bv.size(); ++i)
  {
    if(bv[i].is_true())
      idx_val += power(2, i);
    else if(!bv[i].is_false())
    {
      is_const = false;
      break;
    }
  }
  if(is_const)
  {
    auto it = index_to_bv_object_offset.find(idx_val);
    if(it != index_to_bv_object_offset.end())
      return it->second.first;
  }

  const std::size_t width = type.get_width();
  const unsignedbv_typet bv_type(width);
  // Create a fresh symbol for the index value
  symbol_exprt idx_sym(
    "bv_pointers_wide::ro_idx::" + std::to_string(scope_counter++), bv_type);
  const bvt &idx_bv = convert_bv(idx_sym);
  for(std::size_t i = 0; i < width; ++i)
    prop.set_equal(idx_bv[i], bv[i]);
  return convert_bv(index_exprt(object_map, idx_sym));
}

bvt bv_pointers_widet::read_offset(const bvt &bv, const pointer_typet &type)
{
  // Try direct lookup from the index to avoid array reads
  mp_integer idx_val = 0;
  bool is_const = true;
  for(std::size_t i = 0; i < bv.size(); ++i)
  {
    if(bv[i].is_true())
      idx_val += power(2, i);
    else if(!bv[i].is_false())
    {
      is_const = false;
      break;
    }
  }
  if(is_const)
  {
    auto it = index_to_bv_object_offset.find(idx_val);
    if(it != index_to_bv_object_offset.end())
      return it->second.second;
  }

  const std::size_t width = type.get_width();
  const unsignedbv_typet bv_type(width);
  symbol_exprt idx_sym(
    "bv_pointers_wide::roff_idx::" + std::to_string(scope_counter++), bv_type);
  const bvt &idx_bv = convert_bv(idx_sym);
  for(std::size_t i = 0; i < width; ++i)
    prop.set_equal(idx_bv[i], bv[i]);
  return convert_bv(index_exprt(offset_map, idx_sym));
}

// Get or create a symbolic base address for an object.

bvt bv_pointers_widet::get_object_base_address(
  const mp_integer &object,
  std::size_t width)
{
  auto it = object_base_address.find(object);
  if(it != object_base_address.end())
    return it->second;

  bvt base = prop.new_variables(width);
  object_base_address[object] = base;
  return base;
}

// Encode: allocate a fresh index, constrain the maps.

bvt bv_pointers_widet::encode(
  const mp_integer &object,
  const pointer_typet &type)
{
  // Return cached encoding if available
  auto cache_it = encode_cache.find(object);
  if(cache_it != encode_cache.end())
    return cache_it->second;

  const std::size_t width = type.get_width();
  const unsignedbv_typet bv_type(width);

  mp_integer idx = next_bv_pointer_index;
  ++next_bv_pointer_index;
  exprt idx_expr = from_integer(idx, bv_type);

  // object_map[idx] == object
  set_to(
    equal_exprt(
      index_exprt(object_map, idx_expr), from_integer(object, bv_type)),
    true);

  // offset_map[idx] == 0
  set_to(
    equal_exprt(index_exprt(offset_map, idx_expr), from_integer(0, bv_type)),
    true);

  index_to_object_offset[idx] = {object, mp_integer{0}};

  // Store bitvector-level object/offset for direct lookup
  // in offset_arithmetic (avoids array reads).
  index_to_bv_object_offset[idx] = {
    bv_utils.build_constant(object, width), bv_utils.build_constant(0, width)};

  bvt result = convert_bv(idx_expr);
  encode_cache[object] = result;
  return result;
}

// encode_fresh: like encode but with symbolic object/offset bvs.

bvt bv_pointers_widet::encode_fresh(
  const bvt &object_bv,
  const bvt &offset_bv,
  const pointer_typet &type)
{
  const std::size_t width = type.get_width();
  const unsignedbv_typet bv_type(width);

  mp_integer idx = next_bv_pointer_index;
  ++next_bv_pointer_index;
  exprt idx_expr = from_integer(idx, bv_type);
  bvt index_bv = convert_bv(idx_expr);

  // Constrain object_map[idx] == object_bv
  bvt obj_read = convert_bv(index_exprt(object_map, idx_expr));
  for(std::size_t i = 0; i < width; ++i)
    prop.set_equal(obj_read[i], object_bv[i]);

  // Constrain offset_map[idx] == offset_bv
  bvt off_read = convert_bv(index_exprt(offset_map, idx_expr));
  for(std::size_t i = 0; i < width; ++i)
    prop.set_equal(off_read[i], offset_bv[i]);

  index_to_bv_object_offset[idx] = {object_bv, offset_bv};

  return index_bv;
}

// add_addr: register an object and encode it.

bvt bv_pointers_widet::add_addr(const exprt &expr)
{
  const auto a = pointer_logic.add_object(expr);
  const pointer_typet type = pointer_type(expr.type());
  return encode(a, type);
}

// offset_arithmetic overloads

bvt bv_pointers_widet::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &x)
{
  const std::size_t offset_bits = get_offset_width(type);
  return offset_arithmetic(
    type, bv, 1, bv_utils.build_constant(x, offset_bits));
}

bvt bv_pointers_widet::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &factor,
  const exprt &index)
{
  bvt bv_index = convert_bv(index);

  bv_utilst::representationt rep = index.type().id() == ID_signedbv
                                     ? bv_utilst::representationt::SIGNED
                                     : bv_utilst::representationt::UNSIGNED;

  const std::size_t offset_bits = get_offset_width(type);
  bv_index = bv_utils.extension(bv_index, offset_bits, rep);

  return offset_arithmetic(type, bv, factor, bv_index);
}

bvt bv_pointers_widet::offset_arithmetic(
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

bvt bv_pointers_widet::offset_arithmetic(
  const pointer_typet &type,
  const bvt &bv,
  const mp_integer &factor,
  const bvt &index)
{
  bvt bv_index;

  if(factor == 1)
    bv_index = index;
  else
  {
    bvt bv_factor = bv_utils.build_constant(factor, index.size());
    bv_index = bv_utils.signed_multiplier(index, bv_factor);
  }

  const std::size_t offset_bits = get_offset_width(type);
  bv_index = bv_utils.zero_extension(bv_index, offset_bits);

  bvt obj = read_object(bv, type);
  bvt old_offset = read_offset(bv, type);
  bvt new_offset = bv_utils.add(old_offset, bv_index);
  return encode_fresh(obj, new_offset, type);
}

// convert_address_of_rec

std::optional<bvt> bv_pointers_widet::convert_address_of_rec(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.id() == ID_label)
  {
    return add_addr(expr);
  }
  else if(expr.id() == ID_null_object)
  {
    pointer_typet pt = pointer_type(expr.type());
    return encode(pointer_logic.get_null_object(), pt);
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);
    const exprt &array = index_expr.array();
    const exprt &index = index_expr.index();
    const auto &array_type = to_array_type(array.type());

    pointer_typet type = pointer_type(expr.type());
    const std::size_t bits = boolbv_width(type);

    bvt bv;

    if(array_type.id() == ID_pointer)
    {
      bv = convert_pointer_type(array);
      CHECK_RETURN(bv.size() == bits);
    }
    else if(
      array_type.id() == ID_array || array_type.id() == ID_string_constant)
    {
      auto bv_opt = convert_address_of_rec(array);
      if(!bv_opt.has_value())
        return {};
      bv = std::move(*bv_opt);
      CHECK_RETURN(bv.size() == bits);
    }
    else
      UNREACHABLE;

    auto size = pointer_offset_size(array_type.element_type(), ns);
    CHECK_RETURN(size.has_value() && *size >= 0);

    bv = offset_arithmetic(type, bv, *size, index);
    CHECK_RETURN(bv.size() == bits);

    return std::move(bv);
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr = to_byte_extract_expr(expr);

    auto bv_opt = convert_address_of_rec(byte_extract_expr.op());
    if(!bv_opt.has_value())
      return {};

    pointer_typet type = pointer_type(expr.type());
    const std::size_t bits = boolbv_width(type);
    CHECK_RETURN(bv_opt->size() == bits);

    bvt bv = offset_arithmetic(type, *bv_opt, 1, byte_extract_expr.offset());
    CHECK_RETURN(bv.size() == bits);
    return std::move(bv);
  }
  else if(expr.id() == ID_member)
  {
    const member_exprt &member_expr = to_member_expr(expr);
    const exprt &struct_op = member_expr.compound();

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

      pointer_typet type = pointer_type(expr.type());
      bv = offset_arithmetic(type, bv, *offset);
    }
    else
    {
      INVARIANT(
        struct_op.type().id() == ID_union ||
          struct_op.type().id() == ID_union_tag,
        "member expression should operate on "
        "struct or union");
    }

    return std::move(bv);
  }
  else if(
    expr.is_constant() || expr.id() == ID_string_constant ||
    expr.id() == ID_array)
  {
    return add_addr(expr);
  }
  else if(expr.id() == ID_if)
  {
    const if_exprt &ifex = to_if_expr(expr);

    literalt cond = convert(ifex.cond());

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

// convert_pointer_type

bvt bv_pointers_widet::convert_pointer_type(const exprt &expr)
{
  const pointer_typet &type = to_pointer_type(expr.type());
  const std::size_t bits = boolbv_width(expr.type());

  if(expr.id() == ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(expr).get_identifier();
    return map.get_literals(identifier, type, bits);
  }
  else if(expr.id() == ID_nondet_symbol)
  {
    return prop.new_variables(bits);
  }
  else if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tc = to_typecast_expr(expr);
    const exprt &op = tc.op();
    const typet &op_type = op.type();

    if(op_type.id() == ID_pointer)
      return convert_bv(op);
    else if(
      can_cast_type<bitvector_typet>(op_type) || op_type.id() == ID_bool ||
      op_type.id() == ID_c_enum || op_type.id() == ID_c_enum_tag)
    {
      // Integer-to-pointer cast.
      bvt int_bv = convert_bv(op);
      const std::size_t ptr_width = type.get_width();

      // Check if the integer value is a constant
      mp_integer int_val = 0;
      bool is_const = true;
      for(std::size_t i = 0; i < int_bv.size(); ++i)
      {
        if(int_bv[i].is_true())
          int_val += power(2, i);
        else if(!int_bv[i].is_false())
        {
          is_const = false;
          break;
        }
      }

      if(is_const && int_val == 0)
      {
        // (T*)0 is NULL
        return encode(pointer_logic.get_null_object(), type);
      }
      else if(is_const)
      {
        // For constant non-zero integer addresses, create a
        // dedicated "integer address" object with the constant
        // as its base address and offset 0.
        const auto int_addr_obj = pointer_logic.add_object(constant_exprt(
          integer2bvrep(int_val, ptr_width), unsignedbv_typet(ptr_width)));
        bvt result = encode(int_addr_obj, type);
        integer_address_objects.insert(int_addr_obj);
        // Set the base address to the constant value
        bvt base = get_object_base_address(int_addr_obj, ptr_width);
        bvt val_bv = bv_utils.build_constant(int_val, ptr_width);
        for(std::size_t i = 0; i < ptr_width; ++i)
          prop.set_equal(base[i], val_bv[i]);
        return result;
      }
      else
      {
        // Symbolic integer-to-pointer: create a fresh pointer
        // constrained so base[object] + offset == integer value.
        bvt obj_bv = prop.new_variables(ptr_width);
        bvt off_bv = prop.new_variables(ptr_width);
        bvt int_ext = bv_utils.zero_extension(int_bv, ptr_width);

        const auto &objects = pointer_logic.objects;
        std::size_t number = 0;
        for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
        {
          bvt obj_const = bv_utils.build_constant(number, ptr_width);
          literalt is_this_obj = bv_utils.equal(obj_bv, obj_const);
          if(is_this_obj.is_false())
            continue;

          bvt base = get_object_base_address(number, ptr_width);
          bvt flat = bv_utils.add(base, off_bv);
          for(std::size_t i = 0; i < ptr_width; ++i)
          {
            prop.lcnf({!is_this_obj, !flat[i], int_ext[i]});
            prop.lcnf({!is_this_obj, flat[i], !int_ext[i]});
          }
        }

        return encode_fresh(obj_bv, off_bv, type);
      }
    }
  }
  else if(expr.id() == ID_if)
  {
    return SUB::convert_if(to_if_expr(expr));
  }
  else if(expr.id() == ID_index)
  {
    return SUB::convert_index(to_index_expr(expr));
  }
  else if(expr.id() == ID_member)
  {
    return SUB::convert_member(to_member_expr(expr));
  }
  else if(expr.id() == ID_address_of)
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
  else if(expr.id() == ID_plus)
  {
    const plus_exprt &plus_expr = to_plus_expr(expr);

    bvt bv;
    mp_integer size = 0;
    std::size_t count = 0;

    for(const auto &op : plus_expr.operands())
    {
      if(op.type().id() == ID_pointer)
      {
        count++;
        bv = convert_bv(op);
        CHECK_RETURN(bv.size() == bits);

        typet base_type = to_pointer_type(op.type()).base_type();
        DATA_INVARIANT(
          base_type.id() != ID_empty,
          "no pointer arithmetic over void pointers");
        auto size_opt = pointer_offset_size(base_type, ns);
        CHECK_RETURN(size_opt.has_value() && *size_opt >= 0);
        size = *size_opt;
      }
    }

    INVARIANT(count == 1, "exactly one pointer operand");

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
      sum = bv_utils.add(sum, op);
    }

    return offset_arithmetic(type, bv, size, sum);
  }
  else if(expr.id() == ID_minus)
  {
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

    typet base_type = to_pointer_type(minus_expr.lhs().type()).base_type();
    DATA_INVARIANT(
      base_type.id() != ID_empty, "no pointer arithmetic over void pointers");
    auto element_size_opt = pointer_offset_size(base_type, ns);
    CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);
    return offset_arithmetic(type, bv, *element_size_opt, neg_op1);
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
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
    const auto &fa = to_field_address_expr(expr);
    const typet &compound_type = fa.compound_type();

    auto bv = convert_bitvector(fa.base());

    if(compound_type.id() == ID_struct || compound_type.id() == ID_struct_tag)
    {
      const struct_typet &st =
        compound_type.id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(compound_type))
          : to_struct_type(compound_type);
      auto offset = member_offset(st, fa.component_name(), ns);
      CHECK_RETURN(offset.has_value());

      bv = offset_arithmetic(fa.type(), bv, *offset);
    }
    else if(
      compound_type.id() == ID_union || compound_type.id() == ID_union_tag)
    {
      // nothing to do
    }
    else
    {
      INVARIANT(false, "field address on struct or union");
    }

    return bv;
  }
  else if(expr.id() == ID_element_address)
  {
    const auto &ea = to_element_address_expr(expr);

    auto bv = convert_bitvector(ea.base());

    auto size = pointer_offset_size(ea.element_type(), ns);
    CHECK_RETURN(size.has_value() && *size >= 0);

    bv = offset_arithmetic(ea.type(), bv, *size, ea.index());

    return bv;
  }

  return conversion_failed(expr);
}

// is_pointer_subtraction helper

static bool is_pointer_subtraction(const exprt &expr)
{
  if(expr.id() != ID_minus)
    return false;
  const auto &minus_expr = to_minus_expr(expr);
  return minus_expr.lhs().type().id() == ID_pointer &&
         minus_expr.rhs().type().id() == ID_pointer;
}

// convert_byte_extract: lower when pointers are involved,
// since the abstract pointer index is not meaningful as bytes.

bvt bv_pointers_widet::convert_byte_extract(const byte_extract_exprt &expr)
{
  if(
    has_subtype(expr.type(), ID_pointer, ns) ||
    has_subtype(expr.op().type(), ID_pointer, ns))
  {
    return convert_bv(lower_byte_extract(expr, ns));
  }
  return SUB::convert_byte_extract(expr);
}

// convert_byte_update: lower when pointers are involved.

bvt bv_pointers_widet::convert_byte_update(const byte_update_exprt &expr)
{
  if(
    has_subtype(expr.value().type(), ID_pointer, ns) ||
    has_subtype(expr.op0().type(), ID_pointer, ns))
  {
    return convert_bv(lower_byte_update(expr, ns));
  }
  return SUB::convert_byte_update(expr);
}

// convert_bitvector

bvt bv_pointers_widet::convert_bitvector(const exprt &expr)
{
  if(expr.type().id() == ID_pointer)
    return convert_pointer_type(expr);

  if(is_pointer_subtraction(expr))
  {
    std::size_t width = boolbv_width(expr.type());

    const auto &minus_expr = to_minus_expr(expr);

    const exprt same_obj = ::same_object(minus_expr.lhs(), minus_expr.rhs());
    const literalt same_object_lit = convert(same_obj);

    const pointer_typet &lhs_pt = to_pointer_type(minus_expr.lhs().type());
    const bvt &lhs = convert_bv(minus_expr.lhs());
    const pointer_typet &rhs_pt = to_pointer_type(minus_expr.rhs().type());
    const bvt &rhs = convert_bv(minus_expr.rhs());

    bvt lhs_offset = bv_utils.zero_extension(read_offset(lhs, lhs_pt), width);
    bvt rhs_offset = bv_utils.zero_extension(read_offset(rhs, rhs_pt), width);

    DATA_INVARIANT(
      lhs_pt.base_type().id() != ID_empty,
      "no pointer arithmetic over void pointers");
    auto element_size_opt = pointer_offset_size(lhs_pt.base_type(), ns);
    CHECK_RETURN(element_size_opt.has_value() && *element_size_opt > 0);

    bvt bv = prop.new_variables(width);

    // Same-object case: result = (lhs_offset - rhs_offset) / element_size
    if(!same_object_lit.is_false())
    {
      bvt difference = bv_utils.sub(lhs_offset, rhs_offset);
      if(*element_size_opt != 1)
      {
        bvt element_size_bv = bv_utils.build_constant(*element_size_opt, width);
        difference = bv_utils.divider(
          difference, element_size_bv, bv_utilst::representationt::SIGNED);
      }
      prop.l_set_to_true(
        prop.limplies(same_object_lit, bv_utils.equal(difference, bv)));
    }

    // Different-object case: use flat address difference.
    // This handles integer-address objects like (char*)20-(char*)10.
    if(!same_object_lit.is_true())
    {
      bvt lhs_obj = read_object(lhs, lhs_pt);
      bvt rhs_obj = read_object(rhs, rhs_pt);
      const std::size_t ptr_width = config.ansi_c.pointer_width;

      bvt lhs_flat = lhs_offset;
      bvt rhs_flat = rhs_offset;

      const auto &objects = pointer_logic.objects;
      std::size_t number = 0;
      for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
      {
        auto base_it = object_base_address.find(mp_integer(number));
        if(base_it == object_base_address.end())
          continue;
        bvt obj_const = bv_utils.build_constant(number, ptr_width);
        bvt base_ext = bv_utils.zero_extension(base_it->second, width);

        literalt is_l = bv_utils.equal(lhs_obj, obj_const);
        lhs_flat =
          bv_utils.select(is_l, bv_utils.add(base_ext, lhs_offset), lhs_flat);

        literalt is_r = bv_utils.equal(rhs_obj, obj_const);
        rhs_flat =
          bv_utils.select(is_r, bv_utils.add(base_ext, rhs_offset), rhs_flat);
      }

      bvt flat_diff = bv_utils.sub(lhs_flat, rhs_flat);
      if(*element_size_opt != 1)
      {
        bvt element_size_bv = bv_utils.build_constant(*element_size_opt, width);
        flat_diff = bv_utils.divider(
          flat_diff, element_size_bv, bv_utilst::representationt::SIGNED);
      }
      prop.l_set_to_true(
        prop.limplies(!same_object_lit, bv_utils.equal(flat_diff, bv)));
    }

    return bv;
  }
  else if(
    expr.id() == ID_pointer_offset &&
    to_pointer_offset_expr(expr).pointer().type().id() == ID_pointer)
  {
    std::size_t width = boolbv_width(expr.type());

    const exprt &pointer = to_pointer_offset_expr(expr).pointer();
    const bvt &pointer_bv = convert_bv(pointer);

    bvt offset_bv = read_offset(pointer_bv, to_pointer_type(pointer.type()));

    return bv_utils.zero_extension(offset_bv, width);
  }
  else if(
    const auto object_size = expr_try_dynamic_cast<object_size_exprt>(expr))
  {
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
    std::size_t width = boolbv_width(expr.type());

    const exprt &pointer = to_pointer_object_expr(expr).pointer();
    const bvt &pointer_bv = convert_bv(pointer);

    bvt object_bv = read_object(pointer_bv, to_pointer_type(pointer.type()));

    return bv_utils.zero_extension(object_bv, width);
  }
  else if(
    expr.id() == ID_typecast &&
    to_typecast_expr(expr).op().type().id() == ID_pointer)
  {
    // Pointer-to-integer cast: compute base[object] + offset.
    // For pointers with known constant indices (from encode()),
    // look up the object directly. For symbolic pointers,
    // postpone to finish_eager_conversion.
    const exprt &ptr_op = to_typecast_expr(expr).op();
    const bvt &ptr_bv = convert_bv(ptr_op);
    const pointer_typet &ptr_type = to_pointer_type(ptr_op.type());
    const std::size_t ptr_width = ptr_type.get_width();
    std::size_t width = boolbv_width(expr.type());

    // Try to extract a constant index from the pointer bitvector
    mp_integer idx_val = 0;
    bool is_constant = true;
    for(std::size_t i = 0; i < ptr_bv.size(); ++i)
    {
      if(ptr_bv[i].is_true())
        idx_val += power(2, i);
      else if(!ptr_bv[i].is_false())
      {
        is_constant = false;
        break;
      }
    }

    if(is_constant)
    {
      auto it = index_to_object_offset.find(idx_val);
      if(it != index_to_object_offset.end())
      {
        bvt base = get_object_base_address(it->second.first, ptr_width);
        bvt off_const = bv_utils.build_constant(it->second.second, ptr_width);
        bvt flat = bv_utils.add(base, off_const);
        return bv_utils.zero_extension(flat, width);
      }

      // Also check encode_fresh's bitvector-level map
      auto it2 = index_to_bv_object_offset.find(idx_val);
      if(it2 != index_to_bv_object_offset.end())
      {
        const bvt &obj_bv = it2->second.first;
        const bvt &off_bv = it2->second.second;

        // Try to extract constant object number for base address
        mp_integer obj_val = 0;
        bool obj_is_const = true;
        for(std::size_t i = 0; i < obj_bv.size(); ++i)
        {
          if(obj_bv[i].is_true())
            obj_val += power(2, i);
          else if(!obj_bv[i].is_false())
          {
            obj_is_const = false;
            break;
          }
        }

        if(obj_is_const)
        {
          bvt base = get_object_base_address(obj_val, ptr_width);
          bvt flat = bv_utils.add(base, off_bv);
          return bv_utils.zero_extension(flat, width);
        }
      }
    }

    // For symbolic pointers, postpone
    bvt result = prop.new_variables(width);
    postponed_list.emplace_back(result, ptr_bv, expr);
    return result;
  }

  return SUB::convert_bitvector(expr);
}

// convert_rest

literalt bv_pointers_widet::convert_rest(const exprt &expr)
{
  PRECONDITION(expr.is_boolean());

  // Handle pointer equality/inequality FIRST, before the
  // else-if chain below, to ensure it's always reached.
  if(expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    const auto &rel = to_binary_relation_expr(expr);
    if(
      rel.lhs().type().id() == ID_pointer &&
      rel.rhs().type().id() == ID_pointer)
    {
      const pointer_typet &lhs_type = to_pointer_type(rel.lhs().type());
      const pointer_typet &rhs_type = to_pointer_type(rel.rhs().type());

      const bvt &lhs_bv = convert_bv(rel.lhs());
      const bvt &rhs_bv = convert_bv(rel.rhs());

      literalt indices_equal = bv_utils.equal(lhs_bv, rhs_bv);

      if(indices_equal.is_false())
      {
        // Indices definitely different — semantic comparison
        bvt lhs_obj = read_object(lhs_bv, lhs_type);
        bvt rhs_obj = read_object(rhs_bv, rhs_type);
        bvt lhs_off = read_offset(lhs_bv, lhs_type);
        bvt rhs_off = read_offset(rhs_bv, rhs_type);

        literalt obj_eq = bv_utils.equal(lhs_obj, rhs_obj);
        literalt off_eq = bv_utils.equal(lhs_off, rhs_off);
        literalt result = prop.land(obj_eq, off_eq);

        if(expr.id() == ID_notequal)
          return !result;
        return result;
      }

      // Add semantic comparison for different indices
      bvt lhs_obj = read_object(lhs_bv, lhs_type);
      bvt rhs_obj = read_object(rhs_bv, rhs_type);
      bvt lhs_off = read_offset(lhs_bv, lhs_type);
      bvt rhs_off = read_offset(rhs_bv, rhs_type);

      literalt obj_eq = bv_utils.equal(lhs_obj, rhs_obj);
      literalt off_eq = bv_utils.equal(lhs_off, rhs_off);
      literalt semantic_eq = prop.land(obj_eq, off_eq);

      literalt result = prop.lor(indices_equal, semantic_eq);

      prop.l_set_to_true(prop.limplies(indices_equal, obj_eq));
      prop.l_set_to_true(prop.limplies(indices_equal, off_eq));

      if(expr.id() == ID_notequal)
        return !result;
      return result;
    }
  }

  const exprt::operandst &operands = expr.operands();

  if(expr.id() == ID_is_invalid_pointer)
  {
    if(operands.size() == 1 && operands[0].type().id() == ID_pointer)
    {
      const bvt &bv = convert_bv(operands[0]);

      if(!bv.empty())
      {
        const pointer_typet &type = to_pointer_type(operands[0].type());
        bvt object_bv = read_object(bv, type);

        bvt invalid_bv = bv_utils.build_constant(
          pointer_logic.get_invalid_object(), get_object_width(type));

        const std::size_t object_bits = get_object_width(type);

        bvt equal_bv;
        equal_bv.reserve(object_bits);

        for(std::size_t i = 0; i < object_bits; i++)
        {
          equal_bv.push_back(prop.lequal(object_bv[i], invalid_bv[i]));
        }

        return prop.land(equal_bv);
      }
    }
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    if(operands.size() == 1 && operands[0].type().id() == ID_pointer)
    {
      literalt l = prop.new_variable();
      postponed_list.emplace_back(bvt{1, l}, convert_bv(operands[0]), expr);
      return l;
    }
  }
  else if(
    expr.id() == ID_lt || expr.id() == ID_le || expr.id() == ID_gt ||
    expr.id() == ID_ge)
  {
    if(
      operands.size() == 2 && operands[0].type().id() == ID_pointer &&
      operands[1].type().id() == ID_pointer)
    {
      const bvt &bv0 = convert_bv(operands[0]);
      const bvt &bv1 = convert_bv(operands[1]);

      const pointer_typet &type0 = to_pointer_type(operands[0].type());
      bvt offset_bv0 = read_offset(bv0, type0);

      const pointer_typet &type1 = to_pointer_type(operands[1].type());
      bvt offset_bv1 = read_offset(bv1, type1);

      const exprt same_obj = ::same_object(operands[0], operands[1]);
      const literalt same_object_lit = convert(same_obj);
      if(same_object_lit.is_false())
        return same_object_lit;

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

  else if(
    const auto minus_overflow =
      expr_try_dynamic_cast<minus_overflow_exprt>(expr))
  {
    if(
      minus_overflow->lhs().type().id() == ID_pointer &&
      minus_overflow->rhs().type().id() == ID_pointer)
    {
      // Pointer subtraction overflow: use the offsets from the
      // maps instead of the raw indices.  When both pointers
      // are in the same object, the offsets are bounded by the
      // object size and the difference cannot overflow.
      const pointer_typet &lhs_pt =
        to_pointer_type(minus_overflow->lhs().type());
      const pointer_typet &rhs_pt =
        to_pointer_type(minus_overflow->rhs().type());

      const bvt &lhs_bv = convert_bv(minus_overflow->lhs());
      const bvt &rhs_bv = convert_bv(minus_overflow->rhs());

      // For same-object pointers, check offset overflow.
      // For different-object pointers, the subtraction is
      // undefined — use the flat address difference.
      bvt lhs_obj = read_object(lhs_bv, lhs_pt);
      bvt rhs_obj = read_object(rhs_bv, rhs_pt);
      literalt same_obj = bv_utils.equal(lhs_obj, rhs_obj);

      bvt lhs_off = read_offset(lhs_bv, lhs_pt);
      bvt rhs_off = read_offset(rhs_bv, rhs_pt);

      // Same object: overflow iff offset difference overflows
      literalt off_overflow = bv_utils.overflow_sub(
        lhs_off, rhs_off, bv_utilst::representationt::SIGNED);

      // Different objects: use flat addresses for overflow check
      const std::size_t width = lhs_off.size();
      bvt lhs_flat = lhs_off; // placeholder
      bvt rhs_flat = rhs_off;

      // Try to get flat addresses from base address map
      mp_integer lhs_idx = 0, rhs_idx = 0;
      bool lhs_const = true, rhs_const = true;
      for(std::size_t i = 0; i < lhs_bv.size(); ++i)
      {
        if(lhs_bv[i].is_true())
          lhs_idx += power(2, i);
        else if(!lhs_bv[i].is_false())
          lhs_const = false;
      }
      for(std::size_t i = 0; i < rhs_bv.size(); ++i)
      {
        if(rhs_bv[i].is_true())
          rhs_idx += power(2, i);
        else if(!rhs_bv[i].is_false())
          rhs_const = false;
      }

      if(lhs_const && rhs_const)
      {
        auto lit = index_to_bv_object_offset.find(lhs_idx);
        auto rit = index_to_bv_object_offset.find(rhs_idx);
        if(
          lit != index_to_bv_object_offset.end() &&
          rit != index_to_bv_object_offset.end())
        {
          // Extract object numbers
          mp_integer lobj = 0, robj = 0;
          bool lok = true, rok = true;
          for(std::size_t i = 0; i < lit->second.first.size(); ++i)
          {
            if(lit->second.first[i].is_true())
              lobj += power(2, i);
            else if(!lit->second.first[i].is_false())
              lok = false;
          }
          for(std::size_t i = 0; i < rit->second.first.size(); ++i)
          {
            if(rit->second.first[i].is_true())
              robj += power(2, i);
            else if(!rit->second.first[i].is_false())
              rok = false;
          }
          if(lok && rok)
          {
            bvt lbase = get_object_base_address(lobj, width);
            bvt rbase = get_object_base_address(robj, width);
            lhs_flat = bv_utils.add(lbase, lhs_off);
            rhs_flat = bv_utils.add(rbase, rhs_off);
          }
        }
      }

      literalt flat_overflow = bv_utils.overflow_sub(
        lhs_flat, rhs_flat, bv_utilst::representationt::SIGNED);

      // Overflow if same object and offset overflows, or
      // different objects and flat address overflows
      return prop.lor(
        prop.land(same_obj, off_overflow), prop.land(!same_obj, flat_overflow));
    }
  }

  return SUB::convert_rest(expr);
}

// bits_to_string helper

static std::string bits_to_string(const propt &prop, const bvt &bv)
{
  std::string result;

  for(const auto &literal : bv)
  {
    char ch = 0;

    // clang-format off
    switch(prop.l_get(literal).get_value())
    {
    case tvt::tv_enumt::TV_FALSE: ch='0'; break;
    case tvt::tv_enumt::TV_TRUE:  ch='1'; break;
    case tvt::tv_enumt::TV_UNKNOWN: ch='0'; break;
    }
    // clang-format on

    result = ch + result;
  }

  return result;
}

// bv_get_rec

exprt bv_pointers_widet::bv_get_rec(
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

  const irep_idt bvrep = make_bvrep(
    bits,
    [&value](std::size_t i) { return value[value.size() - 1 - i] == '1'; });

  // The bitvector holds the abstract pointer index.
  // Look up the (object, offset) pair recorded at
  // encode time.
  mp_integer idx_val = binary2integer(value, false);

  auto it = index_to_object_offset.find(idx_val);
  if(it != index_to_object_offset.end())
  {
    pointer_logict::pointert pointer{it->second.first, it->second.second};
    // Try to compute flat address for the hex display
    irep_idt display_bvrep = bvrep;
    auto base_it = object_base_address.find(it->second.first);
    if(base_it != object_base_address.end())
    {
      std::string base_str = bits_to_string(prop, base_it->second);
      mp_integer base_val = binary2integer(base_str, false);
      mp_integer flat_addr = base_val + it->second.second;
      display_bvrep = integer2bvrep(flat_addr, bits);
    }
    return annotated_pointer_constant_exprt{
      display_bvrep, pointer_logic.pointer_expr(pointer, pt)};
  }

  // For indices not tracked by encode(), try encode_fresh's
  // bitvector map and read the model values.
  auto it2 = index_to_bv_object_offset.find(idx_val);
  if(it2 != index_to_bv_object_offset.end())
  {
    std::string obj_str = bits_to_string(prop, it2->second.first);
    std::string off_str = bits_to_string(prop, it2->second.second);
    mp_integer obj_val = binary2integer(obj_str, false);
    mp_integer off_val = binary2integer(off_str, false);
    pointer_logict::pointert pointer{obj_val, off_val};
    // Try to compute flat address
    irep_idt display_bvrep = bvrep;
    auto base_it = object_base_address.find(obj_val);
    if(base_it != object_base_address.end())
    {
      std::string base_str = bits_to_string(prop, base_it->second);
      mp_integer base_val = binary2integer(base_str, false);
      mp_integer flat_addr = base_val + off_val;
      display_bvrep = integer2bvrep(flat_addr, bits);
    }
    return annotated_pointer_constant_exprt{
      display_bvrep, pointer_logic.pointer_expr(pointer, pt)};
  }

  // Truly unknown index — return raw constant.
  return constant_exprt(bvrep, type);
}

// prepare_postponed_is_dynamic_object

std::pair<exprt, exprt> bv_pointers_widet::prepare_postponed_is_dynamic_object(
  std::vector<symbol_exprt> &placeholders) const
{
  PRECONDITION(placeholders.empty());

  const auto &objects = pointer_logic.objects;
  std::size_t number = 0;

  exprt::operandst dynamic_objects_ops;
  exprt::operandst not_dynamic_objects_ops;
  dynamic_objects_ops.reserve(objects.size());
  not_dynamic_objects_ops.reserve(objects.size());

  for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
  {
    const exprt &expr = *it;

    // In the wide encoding the object identity is the
    // object number itself as a constant bitvector.
    pointer_typet pt = pointer_type(expr.type());
    bvt bv = bv_utils.build_constant(number, get_object_width(pt));

    exprt::operandst conjuncts;
    conjuncts.reserve(bv.size());
    placeholders.reserve(bv.size());
    for(std::size_t i = 0; i < bv.size(); ++i)
    {
      if(placeholders.size() <= i)
      {
        placeholders.push_back(symbol_exprt{std::to_string(i), bool_typet{}});
      }

      POSTCONDITION(bv[i].is_constant());
      if(bv[i].is_true())
        conjuncts.emplace_back(placeholders[i]);
      else
        conjuncts.emplace_back(not_exprt{placeholders[i]});
    }

    if(pointer_logic.is_dynamic_object(expr))
      dynamic_objects_ops.push_back(conjunction(conjuncts));
    else
    {
      not_dynamic_objects_ops.push_back(conjunction(conjuncts));
    }
  }

  exprt dynamic_objects = disjunction(dynamic_objects_ops);
  exprt not_dynamic_objects = disjunction(not_dynamic_objects_ops);

  bdd_exprt bdd_converter;
  bddt dyn_bdd = bdd_converter.from_expr(dynamic_objects);
  bddt not_dyn_bdd = bdd_converter.from_expr(not_dynamic_objects);

  return {bdd_converter.as_expr(dyn_bdd), bdd_converter.as_expr(not_dyn_bdd)};
}

// prepare_postponed_object_size

std::unordered_map<exprt, exprt, irep_hash>
bv_pointers_widet::prepare_postponed_object_size(
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
    {
      continue;
    }

    const auto size_expr = size_of_expr(expr.type(), ns);
    if(!size_expr.has_value())
      continue;

    pointer_typet pt = pointer_type(expr.type());
    bvt bv = bv_utils.build_constant(number, get_object_width(pt));

    exprt::operandst conjuncts;
    conjuncts.reserve(bv.size());
    placeholders.reserve(bv.size());
    for(std::size_t i = 0; i < bv.size(); ++i)
    {
      if(placeholders.size() <= i)
      {
        placeholders.push_back(symbol_exprt{std::to_string(i), bool_typet{}});
      }

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

// finish_eager_conversion

void bv_pointers_widet::finish_eager_conversion()
{
  // Pre-read object bitvectors for all postponed entries
  // BEFORE array theory finalization.  read_object() creates
  // solver-level array reads that must be registered before
  // arrayst processes consistency constraints.
  std::vector<bvt> preread_obj;
  std::vector<bvt> preread_off;
  preread_obj.reserve(postponed_list.size());
  preread_off.reserve(postponed_list.size());
  for(const postponedt &postponed : postponed_list)
  {
    if(postponed.expr.id() == ID_is_dynamic_object)
    {
      const auto &type =
        to_pointer_type(to_unary_expr(postponed.expr).op().type());
      preread_obj.push_back(read_object(postponed.op, type));
      preread_off.push_back(bvt{});
    }
    else if(expr_try_dynamic_cast<object_size_exprt>(postponed.expr))
    {
      const auto &type =
        to_pointer_type(expr_try_dynamic_cast<object_size_exprt>(postponed.expr)
                          ->pointer()
                          .type());
      preread_obj.push_back(read_object(postponed.op, type));
      preread_off.push_back(bvt{});
    }
    else if(
      postponed.expr.id() == ID_typecast &&
      to_typecast_expr(postponed.expr).op().type().id() == ID_pointer)
    {
      // Pointer-to-integer cast: pre-read object and offset
      const auto &ptr_type =
        to_pointer_type(to_typecast_expr(postponed.expr).op().type());
      preread_obj.push_back(read_object(postponed.op, ptr_type));
      preread_off.push_back(read_offset(postponed.op, ptr_type));
    }
    else
      UNREACHABLE;
  }

  // Now finalize arrays (and everything else).
  SUB::finish_eager_conversion();

  // Build BDD-optimized Boolean formulas lazily.
  std::pair<exprt, exprt> is_dynamic_expr = {nil_exprt{}, nil_exprt{}};
  std::vector<symbol_exprt> is_dynamic_placeholders;

  std::unordered_map<exprt, exprt, irep_hash> object_sizes;
  std::vector<symbol_exprt> object_size_placeholders;

  std::size_t postponed_idx = 0;

  for(const postponedt &postponed : postponed_list)
  {
    const bvt &saved_obj_bv = preread_obj[postponed_idx];
    ++postponed_idx;

    if(postponed.expr.id() == ID_is_dynamic_object)
    {
      if(is_dynamic_expr.first.is_nil())
      {
        is_dynamic_expr =
          prepare_postponed_is_dynamic_object(is_dynamic_placeholders);
      }

      POSTCONDITION(saved_obj_bv.size() == is_dynamic_placeholders.size());
      replace_mapt replacements;
      for(std::size_t i = 0; i < saved_obj_bv.size(); ++i)
      {
        replacements.emplace(
          is_dynamic_placeholders[i], literal_exprt{saved_obj_bv[i]});
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
      {
        object_sizes = prepare_postponed_object_size(object_size_placeholders);
      }

      // we might not have any usable objects
      if(object_size_placeholders.empty())
        continue;

      POSTCONDITION(saved_obj_bv.size() == object_size_placeholders.size());
      replace_mapt replacements;
      for(std::size_t i = 0; i < saved_obj_bv.size(); ++i)
      {
        replacements.emplace(
          object_size_placeholders[i], literal_exprt{saved_obj_bv[i]});
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
          {
            prop.set_equal(postponed.bv[i], size_bv[i]);
          }
          break;
        }
        else if(l1.is_false())
          continue;

        for(std::size_t i = 0; i < postponed.bv.size(); ++i)
        {
          prop.lcnf({!l1, !postponed.bv[i], size_bv[i]});
          prop.lcnf({!l1, postponed.bv[i], !size_bv[i]});
        }
      }
    }
    else if(
      postponed.expr.id() == ID_typecast &&
      to_typecast_expr(postponed.expr).op().type().id() == ID_pointer)
    {
      // Pointer-to-integer cast: compute base[object] + offset
      // using a MUX chain over all known objects.
      const bvt &obj_bv = saved_obj_bv;
      const bvt &off_bv = preread_off[postponed_idx - 1];
      const std::size_t ptr_width = config.ansi_c.pointer_width;
      const std::size_t result_width = postponed.bv.size();

      bvt result = bv_utils.build_constant(0, result_width);

      const auto &objects = pointer_logic.objects;
      std::size_t obj_number = 0;
      for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++obj_number)
      {
        bvt obj_const = bv_utils.build_constant(obj_number, ptr_width);
        literalt is_this_obj = bv_utils.equal(obj_bv, obj_const);

        if(is_this_obj.is_false())
          continue;

        bvt base = get_object_base_address(obj_number, ptr_width);
        bvt flat = bv_utils.add(base, off_bv);
        bvt flat_ext = bv_utils.zero_extension(flat, result_width);

        result = bv_utils.select(is_this_obj, flat_ext, result);
      }

      // Constrain postponed.bv == result
      for(std::size_t i = 0; i < result_width; ++i)
        prop.set_equal(postponed.bv[i], result[i]);
    }
    else
      UNREACHABLE;
  }

  // Add non-overlapping constraints for base addresses AFTER
  // all P2I casts have been processed (which creates the base
  // address variables).
  {
    const auto &objects = pointer_logic.objects;
    const std::size_t ptr_width = config.ansi_c.pointer_width;

    // Constrain NULL object to have base address 0
    // Always create the NULL base address so it participates
    // in non-overlapping constraints.
    bvt null_base =
      get_object_base_address(pointer_logic.get_null_object(), ptr_width);
    bvt zero_bv = bv_utils.build_constant(0, ptr_width);
    for(std::size_t i = 0; i < ptr_width; ++i)
      prop.set_equal(null_base[i], zero_bv[i]);

    // Collect all objects with base addresses
    std::vector<std::pair<mp_integer, mp_integer>> obj_sizes;
    std::size_t number = 0;
    for(auto it = objects.cbegin(); it != objects.cend(); ++it, ++number)
    {
      if(object_base_address.find(number) == object_base_address.end())
        continue;
      // Skip integer-address objects — they may overlap with
      // regular objects (the integer address might point into
      // an existing object).
      if(integer_address_objects.count(number))
        continue;
      const exprt &expr = *it;
      auto size_opt = pointer_offset_size(expr.type(), ns);
      mp_integer size =
        (size_opt.has_value() && *size_opt > 0) ? *size_opt : mp_integer{1};
      obj_sizes.push_back({mp_integer(number), size});

      // Constrain base address to avoid unsigned overflow:
      // base + size <= 2^width (i.e., base <= MAX - size + 1)
      bvt base = get_object_base_address(mp_integer(number), ptr_width);
      mp_integer max_base = power(2, ptr_width) - size;
      bvt max_base_bv = bv_utils.build_constant(max_base, ptr_width);
      prop.l_set_to_true(bv_utils.rel(
        base, ID_le, max_base_bv, bv_utilst::representationt::UNSIGNED));

      // Also constrain base + size to fit in the positive range
      // of a signed integer of pointer width.  This ensures that
      // pointer-to-integer casts and subsequent arithmetic don't
      // overflow signed types.  On real hardware, user-space
      // addresses are in the lower half of the address space.
      // Use 31 bits (not ptr_width-1) to also handle casts to
      // 32-bit int on 64-bit platforms.
      std::size_t addr_bits = std::min(ptr_width - 1, std::size_t{31});
      mp_integer signed_max = power(2, addr_bits) - 1 - size;
      if(signed_max > 0)
      {
        bvt signed_max_bv = bv_utils.build_constant(signed_max, ptr_width);
        prop.l_set_to_true(bv_utils.rel(
          base, ID_le, signed_max_bv, bv_utilst::representationt::UNSIGNED));
      }

      // Constrain alignment: base addresses are aligned to the
      // natural alignment of the object type.  For most types
      // this is min(size, pointer_width/8).
      mp_integer alignment = std::min(size, mp_integer(ptr_width / 8));
      // Round down to power of 2
      mp_integer align_pow2 = 1;
      while(align_pow2 * 2 <= alignment)
        align_pow2 *= 2;
      if(align_pow2 > 1)
      {
        // base % align_pow2 == 0, i.e., low bits are zero
        std::size_t align_bits = 0;
        mp_integer tmp = align_pow2;
        while(tmp > 1)
        {
          align_bits++;
          tmp /= 2;
        }
        for(std::size_t i = 0; i < align_bits && i < ptr_width; ++i)
          prop.l_set_to_true(!base[i]);
      }
    }

    for(std::size_t i = 0; i < obj_sizes.size(); ++i)
    {
      bvt base_i = get_object_base_address(obj_sizes[i].first, ptr_width);

      for(std::size_t j = i + 1; j < obj_sizes.size(); ++j)
      {
        bvt base_j = get_object_base_address(obj_sizes[j].first, ptr_width);

        bvt end_i = bv_utils.add(
          base_i, bv_utils.build_constant(obj_sizes[i].second, ptr_width));
        literalt i_before_j = bv_utils.rel(
          end_i, ID_le, base_j, bv_utilst::representationt::UNSIGNED);

        bvt end_j = bv_utils.add(
          base_j, bv_utils.build_constant(obj_sizes[j].second, ptr_width));
        literalt j_before_i = bv_utils.rel(
          end_j, ID_le, base_i, bv_utilst::representationt::UNSIGNED);

        // Non-overlapping ranges
        literalt range_lit = prop.lor(i_before_j, j_before_i);
        prop.l_set_to_true(range_lit);
        // Redundant but helps the solver: distinct base addresses
        literalt neq_lit = !bv_utils.equal(base_i, base_j);
        prop.l_set_to_true(neq_lit);

        // Explicit pairwise inequality for all offsets within
        // the smaller object.  The range constraint is logically
        // sufficient but the SAT solver cannot derive these
        // inequalities from it.
        mp_integer max_off = std::max(obj_sizes[i].second, obj_sizes[j].second);
        for(mp_integer k = 0; k < max_off; ++k)
        {
          bvt shifted_i =
            bv_utils.add(base_i, bv_utils.build_constant(k, ptr_width));
          prop.l_set_to_true(!bv_utils.equal(shifted_i, base_j));
          bvt shifted_j =
            bv_utils.add(base_j, bv_utils.build_constant(k, ptr_width));
          prop.l_set_to_true(!bv_utils.equal(shifted_j, base_i));
        }
      }
    }
  }

  postponed_list.clear();
}
