/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_utils.h"

#include "arith_tools.h"
#include "c_types.h"
#include "config.h"
#include "endianness_map.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "pointer_offset_size.h"
#include "std_expr.h"
#include "string_constant.h"
#include "symbol.h"

#include <algorithm>

/// sort operands of an expression according to ordering defined by operator<
/// \par parameters: operand list
/// \return modifies operand list returns true iff nothing was changed
bool sort_operands(exprt::operandst &operands)
{
  bool do_sort=false;

  forall_expr(it, operands)
  {
    exprt::operandst::const_iterator next_it=it;
    next_it++;

    if(next_it!=operands.end() && *next_it < *it)
    {
      do_sort=true;
      break;
    }
  }

  if(!do_sort)
    return true;

  std::sort(operands.begin(), operands.end());

  return false;
}

/// produce canonical ordering for associative and commutative binary operators
// The entries
//  { ID_plus,   ID_floatbv  },
//  { ID_mult,   ID_floatbv  },
//  { ID_plus,   ID_pointer  },
// are deliberately missing, as FP-addition and multiplication
// aren't associative. Addition to pointers isn't really
// associative.

struct saj_tablet
{
  const irep_idt id;
  const irep_idt type_ids[10];
} const saj_table[]=
{
  { ID_plus,  {ID_integer    ,
               ID_natural    ,
               ID_real       ,
               ID_complex    ,
               ID_rational   ,
               ID_unsignedbv ,
               ID_signedbv   ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_mult,  {ID_integer    ,
               ID_natural    ,
               ID_real       ,
               ID_complex    ,
               ID_rational   ,
               ID_unsignedbv ,
               ID_signedbv   ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_and,   {ID_bool       ,
               irep_idt()  }},
  { ID_or,    {ID_bool       ,
               irep_idt()  }},
  { ID_xor,   {ID_bool       ,
               irep_idt()  }},
  { ID_bitand, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitor, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitxor, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { irep_idt(), { irep_idt() }}
};

static bool is_associative_and_commutative_for_type(
  const struct saj_tablet &saj_entry,
  const irep_idt &type_id)
{
  for(unsigned i=0; !saj_entry.type_ids[i].empty(); i++)
    if(type_id==saj_entry.type_ids[i])
      return true;

  return false;
}

static const struct saj_tablet &
get_sort_and_join_table_entry(const irep_idt &id, const irep_idt &type_id)
{
  unsigned i=0;

  for( ; !saj_table[i].id.empty(); i++)
  {
    if(
      id == saj_table[i].id &&
      is_associative_and_commutative_for_type(saj_table[i], type_id))
      return saj_table[i];
  }

  return saj_table[i];
}

static bool sort_and_join(exprt &expr, bool do_sort)
{
  bool no_change = true;

  if(!expr.has_operands())
    return true;

  const struct saj_tablet &saj_entry =
    get_sort_and_join_table_entry(expr.id(), as_const(expr).type().id());
  if(saj_entry.id.empty())
    return true;

  // check operand types

  forall_operands(it, expr)
    if(!is_associative_and_commutative_for_type(saj_entry, it->type().id()))
      return true;

  // join expressions

  exprt::operandst new_ops;
  new_ops.reserve(as_const(expr).operands().size());

  forall_operands(it, expr)
  {
    if(it->id()==expr.id())
    {
      new_ops.reserve(new_ops.capacity()+it->operands().size()-1);

      forall_operands(it2, *it)
        new_ops.push_back(*it2);

      no_change = false;
    }
    else
      new_ops.push_back(*it);
  }

  // sort it
  if(do_sort)
    no_change = sort_operands(new_ops) && no_change;

  if(!no_change)
    expr.operands().swap(new_ops);

  return no_change;
}

bool sort_and_join(exprt &expr)
{
  return sort_and_join(expr, true);
}

bool join_operands(exprt &expr)
{
  return sort_and_join(expr, false);
}

optionalt<exprt> bits2expr(
  const std::string &bits,
  const typet &type,
  bool little_endian,
  const namespacet &ns)
{
  // bits start at lowest memory address
  auto type_bits = pointer_offset_bits(type, ns);

  if(
    !type_bits.has_value() ||
    (type.id() != ID_union && type.id() != ID_union_tag &&
     *type_bits != bits.size()) ||
    ((type.id() == ID_union || type.id() == ID_union_tag) &&
     *type_bits < bits.size()))
  {
    return {};
  }

  if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_floatbv || type.id() == ID_fixedbv ||
    type.id() == ID_c_bit_field || type.id() == ID_pointer ||
    type.id() == ID_bv || type.id() == ID_c_bool)
  {
    if(
      type.id() == ID_pointer && config.ansi_c.NULL_is_zero &&
      bits.find('1') == std::string::npos)
    {
      return null_pointer_exprt(to_pointer_type(type));
    }

    endianness_mapt map(type, little_endian, ns);

    std::string tmp = bits;
    for(std::string::size_type i = 0; i < bits.size(); ++i)
      tmp[i] = bits[map.map_bit(i)];

    std::reverse(tmp.begin(), tmp.end());

    mp_integer i = binary2integer(tmp, false);
    return constant_exprt(integer2bvrep(i, bits.size()), type);
  }
  else if(type.id() == ID_c_enum)
  {
    auto val = bits2expr(
      bits, to_c_enum_type(type).underlying_type(), little_endian, ns);
    if(val.has_value())
    {
      val->type() = type;
      return *val;
    }
    else
      return {};
  }
  else if(type.id() == ID_c_enum_tag)
  {
    auto val = bits2expr(
      bits, ns.follow_tag(to_c_enum_tag_type(type)), little_endian, ns);
    if(val.has_value())
    {
      val->type() = type;
      return *val;
    }
    else
      return {};
  }
  else if(type.id() == ID_union)
  {
    // find a suitable member
    const union_typet &union_type = to_union_type(type);
    const union_typet::componentst &components = union_type.components();

    for(const auto &component : components)
    {
      auto val = bits2expr(bits, component.type(), little_endian, ns);
      if(!val.has_value())
        continue;

      return union_exprt(component.get_name(), *val, type);
    }
  }
  else if(type.id() == ID_union_tag)
  {
    auto val = bits2expr(
      bits, ns.follow_tag(to_union_tag_type(type)), little_endian, ns);
    if(val.has_value())
    {
      val->type() = type;
      return *val;
    }
    else
      return {};
  }
  else if(type.id() == ID_struct)
  {
    const struct_typet &struct_type = to_struct_type(type);
    const struct_typet::componentst &components = struct_type.components();

    struct_exprt result({}, type);
    result.reserve_operands(components.size());

    mp_integer m_offset_bits = 0;
    for(const auto &component : components)
    {
      const auto m_size = pointer_offset_bits(component.type(), ns);
      CHECK_RETURN(m_size.has_value() && *m_size >= 0);

      std::string comp_bits = std::string(
        bits,
        numeric_cast_v<std::size_t>(m_offset_bits),
        numeric_cast_v<std::size_t>(*m_size));

      auto comp = bits2expr(comp_bits, component.type(), little_endian, ns);
      if(!comp.has_value())
        return {};
      result.add_to_operands(std::move(*comp));

      m_offset_bits += *m_size;
    }

    return std::move(result);
  }
  else if(type.id() == ID_struct_tag)
  {
    auto val = bits2expr(
      bits, ns.follow_tag(to_struct_tag_type(type)), little_endian, ns);
    if(val.has_value())
    {
      val->type() = type;
      return *val;
    }
    else
      return {};
  }
  else if(type.id() == ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    const auto &size_expr = array_type.size();

    PRECONDITION(size_expr.is_constant());

    const std::size_t number_of_elements =
      numeric_cast_v<std::size_t>(to_constant_expr(size_expr));

    const auto el_size_opt = pointer_offset_bits(array_type.element_type(), ns);
    CHECK_RETURN(el_size_opt.has_value() && *el_size_opt > 0);

    const std::size_t el_size = numeric_cast_v<std::size_t>(*el_size_opt);

    array_exprt result({}, array_type);
    result.reserve_operands(number_of_elements);

    for(std::size_t i = 0; i < number_of_elements; ++i)
    {
      std::string el_bits = std::string(bits, i * el_size, el_size);
      auto el =
        bits2expr(el_bits, array_type.element_type(), little_endian, ns);
      if(!el.has_value())
        return {};
      result.add_to_operands(std::move(*el));
    }

    return std::move(result);
  }
  else if(type.id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(type);

    const std::size_t n_el = numeric_cast_v<std::size_t>(vector_type.size());

    const auto el_size_opt =
      pointer_offset_bits(vector_type.element_type(), ns);
    CHECK_RETURN(el_size_opt.has_value() && *el_size_opt > 0);

    const std::size_t el_size = numeric_cast_v<std::size_t>(*el_size_opt);

    vector_exprt result({}, vector_type);
    result.reserve_operands(n_el);

    for(std::size_t i = 0; i < n_el; ++i)
    {
      std::string el_bits = std::string(bits, i * el_size, el_size);
      auto el =
        bits2expr(el_bits, vector_type.element_type(), little_endian, ns);
      if(!el.has_value())
        return {};
      result.add_to_operands(std::move(*el));
    }

    return std::move(result);
  }
  else if(type.id() == ID_complex)
  {
    const complex_typet &complex_type = to_complex_type(type);

    const auto sub_size_opt = pointer_offset_bits(complex_type.subtype(), ns);
    CHECK_RETURN(sub_size_opt.has_value() && *sub_size_opt > 0);

    const std::size_t sub_size = numeric_cast_v<std::size_t>(*sub_size_opt);

    auto real = bits2expr(
      bits.substr(0, sub_size), complex_type.subtype(), little_endian, ns);
    auto imag = bits2expr(
      bits.substr(sub_size), complex_type.subtype(), little_endian, ns);
    if(!real.has_value() || !imag.has_value())
      return {};

    return complex_exprt(*real, *imag, complex_type);
  }

  return {};
}

optionalt<std::string>
expr2bits(const exprt &expr, bool little_endian, const namespacet &ns)
{
  // extract bits from lowest to highest memory address
  const typet &type = expr.type();

  if(expr.id() == ID_constant)
  {
    const auto &value = to_constant_expr(expr).get_value();

    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_floatbv || type.id() == ID_fixedbv ||
      type.id() == ID_c_bit_field || type.id() == ID_bv ||
      type.id() == ID_c_bool)
    {
      const auto width = to_bitvector_type(type).get_width();

      endianness_mapt map(type, little_endian, ns);

      std::string result(width, ' ');

      for(std::string::size_type i = 0; i < width; ++i)
        result[map.map_bit(i)] = get_bvrep_bit(value, width, i) ? '1' : '0';

      return result;
    }
    else if(type.id() == ID_pointer)
    {
      if(value == ID_NULL && config.ansi_c.NULL_is_zero)
        return std::string(to_bitvector_type(type).get_width(), '0');
      else
        return {};
    }
    else if(type.id() == ID_c_enum_tag)
    {
      const auto &c_enum_type = ns.follow_tag(to_c_enum_tag_type(type));
      return expr2bits(constant_exprt(value, c_enum_type), little_endian, ns);
    }
    else if(type.id() == ID_c_enum)
    {
      return expr2bits(
        constant_exprt(value, to_c_enum_type(type).underlying_type()),
        little_endian,
        ns);
    }
  }
  else if(expr.id() == ID_string_constant)
  {
    return expr2bits(
      to_string_constant(expr).to_array_expr(), little_endian, ns);
  }
  else if(expr.id() == ID_union)
  {
    return expr2bits(to_union_expr(expr).op(), little_endian, ns);
  }
  else if(
    expr.id() == ID_struct || expr.id() == ID_array || expr.id() == ID_vector ||
    expr.id() == ID_complex)
  {
    std::string result;
    forall_operands(it, expr)
    {
      auto tmp = expr2bits(*it, little_endian, ns);
      if(!tmp.has_value())
        return {}; // failed
      result += tmp.value();
    }

    return result;
  }

  return {};
}

optionalt<std::reference_wrapper<const array_exprt>>
try_get_string_data_array(const exprt &content, const namespacet &ns)
{
  if(content.id() != ID_address_of)
  {
    return {};
  }

  const auto &array_pointer = to_address_of_expr(content);

  if(array_pointer.object().id() != ID_index)
  {
    return {};
  }

  const auto &array_start = to_index_expr(array_pointer.object());

  if(
    array_start.array().id() != ID_symbol ||
    array_start.array().type().id() != ID_array)
  {
    return {};
  }

  const auto &array = to_symbol_expr(array_start.array());

  const symbolt *symbol_ptr = nullptr;

  if(
    ns.lookup(array.get_identifier(), symbol_ptr) ||
    symbol_ptr->value.id() != ID_array)
  {
    return {};
  }

  const auto &char_seq = to_array_expr(symbol_ptr->value);

  return optionalt<std::reference_wrapper<const array_exprt>>(char_seq);
}
