/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#include "interpreter_class.h"

#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/string_container.h>

#include <langapi/language_util.h>
#include <util/byte_operators.h>

/// Reads a memory address and loads it into the `dest` variable.
/// Marks cell as `READ_BEFORE_WRITTEN` if cell has never been written.
void interpretert::read(
  const mp_integer &address,
  mp_vectort &dest) const
{
  // copy memory region
  for(std::size_t i=0; i<dest.size(); ++i)
  {
    mp_integer value;

    if((address+i)<memory.size())
    {
      const memory_cellt &cell=memory[integer2ulong(address+i)];
      value=cell.value;
      if(cell.initialized==memory_cellt::initializedt::UNKNOWN)
        cell.initialized=memory_cellt::initializedt::READ_BEFORE_WRITTEN;
    }
    else
      value=0;

    dest[i]=value;
  }
}

void interpretert::read_unbounded(
  const mp_integer &address,
  mp_vectort &dest) const
{
  // copy memory region
  std::size_t address_val=integer2size_t(address);
  const mp_integer offset=address_to_offset(address_val);
  const mp_integer alloc_size=
    base_address_to_actual_size(address_val-offset);
  const mp_integer to_read=alloc_size-offset;
  for(size_t i=0; i<to_read; i++)
  {
    mp_integer value;

    if((address+i)<memory.size())
    {
      const memory_cellt &cell=memory[integer2size_t(address+i)];
      value=cell.value;
      if(cell.initialized==memory_cellt::initializedt::UNKNOWN)
        cell.initialized=memory_cellt::initializedt::READ_BEFORE_WRITTEN;
    }
    else
      value=0;

    dest.push_back(value);
  }
}

/// reserves memory block of size at address
void interpretert::allocate(
  const mp_integer &address,
  const mp_integer &size)
{
  // clear memory region
  for(mp_integer i=0; i<size; ++i)
  {
    if((address+i)<memory.size())
    {
      memory_cellt &cell=memory[integer2ulong(address+i)];
      cell.value=0;
      cell.initialized=memory_cellt::initializedt::UNKNOWN;
    }
  }
}

/// Clears memoy r/w flag initialization
void interpretert::clear_input_flags()
{
  for(auto &cell : memory)
  {
    if(cell.second.initialized==
       memory_cellt::initializedt::WRITTEN_BEFORE_READ)
      cell.second.initialized=memory_cellt::initializedt::UNKNOWN;
  }
}

/// Count the number of leaf subtypes of `ty`, a leaf type is a type that is
/// not an array or a struct. For instance the count for a type such as
/// `struct { (int[3])[5]; int }` would be 16 = (3 * 5 + 1).
/// \param ty: a type
/// \param [out] result: Number of leaf primitive types in `ty`
/// \return returns true on error
bool interpretert::count_type_leaves(const typet &ty, mp_integer &result)
{
  if(ty.id()==ID_struct)
  {
    result=0;
    mp_integer subtype_count;
    for(const auto &component : to_struct_type(ty).components())
    {
      if(count_type_leaves(component.type(), subtype_count))
        return true;
      result+=subtype_count;
    }
    return false;
  }
  else if(ty.id()==ID_array)
  {
    const auto &at=to_array_type(ty);
    mp_vectort array_size_vec;
    evaluate(at.size(), array_size_vec);
    if(array_size_vec.size()!=1)
      return true;
    mp_integer subtype_count;
    if(count_type_leaves(at.subtype(), subtype_count))
      return true;
    result=array_size_vec[0]*subtype_count;
    return false;
  }
  else
  {
    result=1;
    return false;
  }
}

/// Supposing the caller has an mp_vector representing a value with type
/// 'source_type', this yields the offset into that vector at which to find a
/// value at *byte* address 'offset'. We need this because the interpreter's
/// memory map uses unlabelled variable-width values -- for example, a C value {
/// { 1, 2 }, 3, 4 } of type struct { int x[2]; char y; unsigned long z; } would
/// be represented [1,2,3,4], with the source type needed alongside to figure
/// out which member is targeted by a byte-extract operation.
/// \par parameters: 'source_type', 'offset' (unit: bytes),
/// \return Offset into a vector of interpreter values; returns true on error
bool interpretert::byte_offset_to_memory_offset(
  const typet &source_type,
  const mp_integer &offset,
  mp_integer &result)
{
  if(source_type.id()==ID_struct)
  {
    const auto &st=to_struct_type(source_type);
    mp_integer previous_member_offsets=0;

    for(const auto &comp : st.components())
    {
      const auto comp_offset = member_offset(st, comp.get_name(), ns);

      const auto component_byte_size = pointer_offset_size(comp.type(), ns);

      if(!comp_offset.has_value() && !component_byte_size.has_value())
        return true;

      if(*comp_offset + *component_byte_size > offset)
      {
        mp_integer subtype_result;
        bool ret = byte_offset_to_memory_offset(
          comp.type(), offset - *comp_offset, subtype_result);
        result=previous_member_offsets+subtype_result;
        return ret;
      }
      else
      {
        mp_integer component_count;
        if(count_type_leaves(comp.type(), component_count))
          return true;
        previous_member_offsets+=component_count;
      }
    }
    // Ran out of struct members, or struct contained a variable-length field.
    return true;
  }
  else if(source_type.id()==ID_array)
  {
    const auto &at=to_array_type(source_type);

    mp_vectort array_size_vec;
    evaluate(at.size(), array_size_vec);

    if(array_size_vec.size()!=1)
      return true;

    mp_integer array_size=array_size_vec[0];
    auto elem_size_bytes = pointer_offset_size(at.subtype(), ns);
    if(!elem_size_bytes.has_value() || *elem_size_bytes == 0)
      return true;

    mp_integer elem_size_leaves;
    if(count_type_leaves(at.subtype(), elem_size_leaves))
      return true;

    mp_integer this_idx = offset / (*elem_size_bytes);
    if(this_idx>=array_size_vec[0])
      return true;

    mp_integer subtype_result;
    bool ret = byte_offset_to_memory_offset(
      at.subtype(), offset % (*elem_size_bytes), subtype_result);

    result=subtype_result+(elem_size_leaves*this_idx);
    return ret;
  }
  else
  {
    result=0;
    // Can't currently subdivide a primitive.
    return offset!=0;
  }
}

/// Similarly to the above, the interpreter's memory objects contain mp_integers
/// that represent variable-sized struct members. This counts the size of type
/// leaves to determine the byte offset corresponding to a memory offset.
/// \par parameters: An interpreter memory offset and the type to interpret that
///   memory
/// \return The corresponding byte offset. Returns true on error
bool interpretert::memory_offset_to_byte_offset(
  const typet &source_type,
  const mp_integer &full_cell_offset,
  mp_integer &result)
{
  if(source_type.id()==ID_struct)
  {
    const auto &st=to_struct_type(source_type);
    mp_integer cell_offset=full_cell_offset;

    for(const auto &comp : st.components())
    {
      mp_integer component_count;
      if(count_type_leaves(comp.type(), component_count))
        return true;
      if(component_count>cell_offset)
      {
        mp_integer subtype_result;
        bool ret=memory_offset_to_byte_offset(
          comp.type(), cell_offset, subtype_result);
        const auto member_offset_result =
          member_offset(st, comp.get_name(), ns);
        CHECK_RETURN(member_offset_result.has_value());
        result = member_offset_result.value() + subtype_result;
        return ret;
      }
      else
      {
        cell_offset-=component_count;
      }
    }
    // Ran out of members, or member of indefinite size
    return true;
  }
  else if(source_type.id()==ID_array)
  {
    const auto &at=to_array_type(source_type);

    mp_vectort array_size_vec;
    evaluate(at.size(), array_size_vec);
    if(array_size_vec.size()!=1)
      return true;

    auto elem_size = pointer_offset_size(at.subtype(), ns);
    if(!elem_size.has_value())
      return true;

    mp_integer elem_count;
    if(count_type_leaves(at.subtype(), elem_count))
      return true;

    mp_integer this_idx=full_cell_offset/elem_count;
    if(this_idx>=array_size_vec[0])
      return true;

    mp_integer subtype_result;
    bool ret=
      memory_offset_to_byte_offset(
        at.subtype(),
        full_cell_offset%elem_count,
        subtype_result);
    result = subtype_result + ((*elem_size) * this_idx);
    return ret;
  }
  else
  {
    // Primitive type.
    result=0;
    return full_cell_offset!=0;
  }
}

/// Evaluate an expression
/// \param expr: expression to evaluate
/// \param [out] dest: vector in which the result of the evaluation is stored
void interpretert::evaluate(
  const exprt &expr,
  mp_vectort &dest)
{
  if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_struct)
    {
      dest.reserve(integer2size_t(get_size(expr.type())));
      bool error=false;

      forall_operands(it, expr)
      {
        if(it->type().id()==ID_code)
          continue;

        mp_integer sub_size=get_size(it->type());
        if(sub_size==0)
          continue;

        mp_vectort tmp;
        evaluate(*it, tmp);

        if(tmp.size()==sub_size)
        {
          for(std::size_t i=0; i<tmp.size(); ++i)
            dest.push_back(tmp[i]);
        }
        else
          error=true;
      }

      if(!error)
        return;

      dest.clear();
    }
    else if(expr.type().id() == ID_pointer)
    {
      mp_integer i=0;
      if(expr.has_operands() && expr.op0().id()==ID_address_of)
      {
        evaluate(expr.op0(), dest);
        return;
      }
      else if(expr.has_operands() && !to_integer(expr.op0(), i))
      {
        dest.push_back(i);
        return;
      }
      // check if expression is constant null pointer without operands
      else if(
        !expr.has_operands() && !to_integer(to_constant_expr(expr), i) &&
        i.is_zero())
      {
        dest.push_back(i);
        return;
      }
    }
    else if(expr.type().id()==ID_floatbv)
    {
      ieee_floatt f;
      f.from_expr(to_constant_expr(expr));
      dest.push_back(f.pack());
      return;
    }
    else if(expr.type().id()==ID_fixedbv)
    {
      fixedbvt f;
      f.from_expr(to_constant_expr(expr));
      dest.push_back(f.get_value());
      return;
    }
    else if(expr.type().id()==ID_c_bool)
    {
      const irep_idt &value=to_constant_expr(expr).get_value();
      dest.push_back(bv2integer(id2string(value), false));
      return;
    }
    else if(expr.type().id()==ID_bool)
    {
      dest.push_back(expr.is_true());
      return;
    }
    else if(expr.type().id()==ID_string)
    {
      const std::string &value = id2string(to_constant_expr(expr).get_value());
      if(show)
        warning() << "string decoding not fully implemented "
                  << value.size() + 1 << eom;
      dest.push_back(get_string_container()[value]);
      return;
    }
    else
    {
      mp_integer i;
      if(!to_integer(expr, i))
      {
        dest.push_back(i);
        return;
      }
    }
  }
  else if(expr.id()==ID_struct)
  {
    if(!unbounded_size(expr.type()))
      dest.reserve(integer2size_t(get_size(expr.type())));

    bool error=false;

    forall_operands(it, expr)
    {
      if(it->type().id()==ID_code)
        continue;

      mp_integer sub_size=get_size(it->type());
      if(sub_size==0)
        continue;

      mp_vectort tmp;
      evaluate(*it, tmp);

      if(unbounded_size(it->type()) || tmp.size()==sub_size)
      {
        for(std::size_t i=0; i<tmp.size(); i++)
          dest.push_back(tmp[i]);
      }
      else
        error=true;
    }

    if(!error)
      return;

    dest.clear();
  }
  else if(expr.id()==ID_side_effect)
  {
    side_effect_exprt side_effect=to_side_effect_expr(expr);
    if(side_effect.get_statement()==ID_nondet)
    {
      if(show)
        error() << "nondet not implemented" << eom;
      return;
    }
    else if(side_effect.get_statement()==ID_allocate)
    {
      if(show)
        error() << "heap memory allocation not fully implemented "
                << expr.type().subtype().pretty()
                << eom;
      std::stringstream buffer;
      num_dynamic_objects++;
      buffer << "interpreter::dynamic_object" << num_dynamic_objects;
      irep_idt id(buffer.str().c_str());
      mp_integer address=build_memory_map(id, expr.type().subtype());
      // TODO: check array of type
      // TODO: interpret zero-initialization argument
      dest.push_back(address);
      return;
    }
    if(show)
      error() << "side effect not implemented "
              << side_effect.get_statement()
              << eom;
  }
  else if(expr.id()==ID_bitor)
  {
    auto const &bitor_expr = to_bitor_expr(expr);
    mp_integer final=0;
    forall_operands(it, bitor_expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1)
        final=bitwise_or(final, tmp.front());
    }
    dest.push_back(final);
    return;
  }
  else if(expr.id()==ID_bitand)
  {
    auto const &bitand_expr = to_bitand_expr(expr);

    mp_integer final=-1;
    forall_operands(it, bitand_expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1)
        final=bitwise_and(final, tmp.front());
    }
    dest.push_back(final);
    return;
  }
  else if(expr.id()==ID_bitxor)
  {
    auto const &bitxor_expr = to_bitxor_expr(expr);

    mp_integer final=0;
    forall_operands(it, bitxor_expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1)
        final=bitwise_xor(final, tmp.front());
    }
    dest.push_back(final);
    return;
  }
  else if(expr.id()==ID_bitnot)
  {
    auto const &bitnot_expr = to_bitnot_expr(expr);
    mp_vectort tmp;
    evaluate(bitnot_expr.op(), tmp);
    if(tmp.size()==1)
    {
      const auto width = to_bitvector_type(expr.op0().type()).get_width();
      const mp_integer mask = power(2, width) - 1;
      dest.push_back(bitwise_xor(tmp.front(), mask));
      return;
    }
  }
  else if(expr.id()==ID_shl)
  {
    auto const &shl_expr = to_shift_expr(expr);

    mp_vectort op, distance;
    evaluate(shl_expr.op(), op);
    evaluate(shl_expr.distance(), distance);
    if(op.size() == 1 && distance.size() == 1)
    {
      mp_integer final = arith_left_shift(
        op.front(),
        distance.front(),
        to_bitvector_type(shl_expr.op().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if((expr.id()==ID_shr) || (expr.id()==ID_lshr))
  {
    auto const &shr_or_lshr_expr = to_shift_expr(expr);

    mp_vectort op, distance;
    evaluate(shr_or_lshr_expr.op(), op);
    evaluate(shr_or_lshr_expr.distance(), distance);
    if(op.size() == 1 && distance.size() == 1)
    {
      mp_integer final = logic_right_shift(
        op.front(),
        distance.front(),
        to_bitvector_type(shr_or_lshr_expr.op().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_ashr)
  {
    auto const &ashr_expr = to_shift_expr(expr);
    mp_vectort op, distance;
    evaluate(ashr_expr.op(), op);
    evaluate(ashr_expr.distance(), distance);
    if(op.size() == 1 && distance.size() == 1)
    {
      mp_integer final = arith_right_shift(
        op.front(),
        distance.front(),
        to_bitvector_type(ashr_expr.op().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_ror)
  {
    auto const &ror_expr = to_shift_expr(expr);
    mp_vectort op, distance;
    evaluate(ror_expr.op(), op);
    evaluate(ror_expr.distance(), distance);
    if(op.size() == 1 && distance.size() == 1)
    {
      mp_integer final = rotate_right(
        op.front(),
        distance.front(),
        to_bitvector_type(ror_expr.op().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_rol)
  {
    auto const &rol_expr = to_shift_expr(expr);

    mp_vectort op, distance;
    evaluate(rol_expr.op(), op);
    evaluate(rol_expr.distance(), distance);
    if(op.size() == 1 && distance.size() == 1)
    {
      mp_integer final = rotate_left(
        op.front(),
        distance.front(),
        to_bitvector_type(rol_expr.op().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal ||
          expr.id()==ID_le ||
          expr.id()==ID_ge ||
          expr.id()==ID_lt ||
          expr.id()==ID_gt)
  {
    auto const &relation_expr = to_binary_relation_expr(expr);

    mp_vectort lhs, rhs;
    evaluate(relation_expr.lhs(), lhs);
    evaluate(relation_expr.rhs(), rhs);

    if(lhs.size() == 1 && rhs.size() == 1)
    {
      const mp_integer &lhs_as_integer = lhs.front();
      const mp_integer &rhs_as_integer = rhs.front();

      if(expr.id()==ID_equal)
        dest.push_back(lhs_as_integer == rhs_as_integer);
      else if(expr.id()==ID_notequal)
        dest.push_back(lhs_as_integer != rhs_as_integer);
      else if(expr.id()==ID_le)
        dest.push_back(lhs_as_integer <= rhs_as_integer);
      else if(expr.id()==ID_ge)
        dest.push_back(lhs_as_integer >= rhs_as_integer);
      else if(expr.id()==ID_lt)
        dest.push_back(lhs_as_integer < rhs_as_integer);
      else if(expr.id()==ID_gt)
        dest.push_back(lhs_as_integer > rhs_as_integer);
    }

    return;
  }
  else if(expr.id()==ID_or)
  {
    auto const &or_expr = to_or_expr(expr);

    bool result=false;

    forall_operands(it, or_expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);

      if(tmp.size()==1 && tmp.front()!=0)
      {
        result=true;
        break;
      }
    }

    dest.push_back(result);

    return;
  }
  else if(expr.id()==ID_if)
  {
    auto const &if_expr = to_if_expr(expr);

    mp_vectort condition, if_result;
    evaluate(if_expr.cond(), condition);

    if(condition.size() == 1)
    {
      if(condition.front() != 0)
        evaluate(if_expr.true_case(), if_result);
      else
        evaluate(if_expr.false_case(), if_result);
    }

    if(if_result.size() == 1)
      dest.push_back(if_result.front());

    return;
  }
  else if(expr.id()==ID_and)
  {
    auto const &and_expr = to_and_expr(expr);

    bool result=true;

    forall_operands(it, and_expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);

      if(tmp.size()==1 && tmp.front()==0)
      {
        result=false;
        break;
      }
    }

    dest.push_back(result);

    return;
  }
  else if(expr.id()==ID_not)
  {
    auto const &not_expr = to_not_expr(expr);

    mp_vectort result_before_not;
    evaluate(not_expr.op(), result_before_not);

    if(result_before_not.size() == 1)
      dest.push_back(result_before_not.front() == 0);

    return;
  }
  else if(expr.id()==ID_plus)
  {
    auto const &plus_expr = to_plus_expr(expr);
    mp_integer result=0;
    forall_operands(it, plus_expr)
    {
      mp_vectort operand;
      evaluate(*it, operand);
      if(operand.size() == 1)
        result += operand.front();
    }

    dest.push_back(result);
    return;
  }
  else if(expr.id()==ID_mult)
  {
    auto const &mult_expr = to_mult_expr(expr);
    // type-dependent!
    mp_integer result;

    if(expr.type().id()==ID_fixedbv)
    {
      fixedbvt f;
      f.spec = fixedbv_spect(to_fixedbv_type(mult_expr.type()));
      f.from_integer(1);
      result=f.get_value();
    }
    else if(expr.type().id()==ID_floatbv)
    {
      ieee_floatt f(to_floatbv_type(mult_expr.type()));
      f.from_integer(1);
      result=f.pack();
    }
    else
      result=1;

    forall_operands(it, mult_expr)
    {
      mp_vectort operand;
      evaluate(*it, operand);
      if(operand.size() == 1)
      {
        if(mult_expr.type().id() == ID_fixedbv)
        {
          fixedbvt f1, f2;
          f1.spec = fixedbv_spect(to_fixedbv_type(mult_expr.type()));
          f2.spec=fixedbv_spect(to_fixedbv_type(it->type()));
          f1.set_value(result);
          f2.set_value(operand.front());
          f1*=f2;
          result=f1.get_value();
        }
        else if(mult_expr.type().id() == ID_floatbv)
        {
          ieee_floatt f1(to_floatbv_type(mult_expr.type()));
          ieee_floatt f2(to_floatbv_type(it->type()));
          f1.unpack(result);
          f2.unpack(operand.front());
          f1*=f2;
          result=f2.pack();
        }
        else
          result *= operand.front();
      }
    }

    dest.push_back(result);
    return;
  }
  else if(expr.id()==ID_minus)
  {
    auto const &minus_expr = to_minus_expr(expr);

    mp_vectort minuend, subtrahend;
    evaluate(minus_expr.op0(), minuend);
    evaluate(minus_expr.op1(), subtrahend);

    if(minuend.size() == 1 && subtrahend.size() == 1)
      dest.push_back(minuend.front() - subtrahend.front());
    return;
  }
  else if(expr.id()==ID_div)
  {
    auto const &div_expr = to_div_expr(expr);

    mp_vectort dividend, divisor;
    evaluate(div_expr.dividend(), dividend);
    evaluate(div_expr.divisor(), divisor);

    if(dividend.size() == 1 && divisor.size() == 1)
      dest.push_back(dividend.front() / divisor.front());
    return;
  }
  else if(expr.id()==ID_unary_minus)
  {
    auto const &unary_minus_expr = to_unary_minus_expr(expr);

    mp_vectort negated;
    evaluate(unary_minus_expr.op(), negated);

    if(negated.size() == 1)
      dest.push_back(-negated.front());
    return;
  }
  else if(expr.id()==ID_address_of)
  {
    auto const &address_of_expr = to_address_of_expr(expr);
    dest.push_back(evaluate_address(address_of_expr.op()));
    return;
  }
  else if(expr.id()==ID_pointer_offset)
  {
    auto const &pointer_offset_expr = to_pointer_offset_expr(expr);
    mp_vectort result;
    evaluate(pointer_offset_expr.op(), result);
    if(result.size()==1)
    {
      // Return the distance, in bytes, between the address returned
      // and the beginning of the underlying object.
      mp_integer address=result[0];
      if(address>0 && address<memory.size())
      {
        auto obj_type=get_type(address_to_identifier(address));

        mp_integer offset=address_to_offset(address);
        mp_integer byte_offset;
        if(!memory_offset_to_byte_offset(obj_type, offset, byte_offset))
          dest.push_back(byte_offset);
      }
    }
    return;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    auto const &byte_extract_expr = to_byte_extract_expr(expr);
    mp_vectort extract_offset;
    evaluate(byte_extract_expr.offset(), extract_offset);
    mp_vectort extract_from;
    evaluate(byte_extract_expr.op(), extract_from);
    if(extract_offset.size()==1 && extract_from.size()!=0)
    {
      const typet &target_type=expr.type();
      mp_integer memory_offset;
      // If memory offset is found (which should normally be the case)
      // extract the corresponding data from the appropriate memory location
      if(!byte_offset_to_memory_offset(
           byte_extract_expr.op().type(), extract_offset[0], memory_offset))
      {
        mp_integer target_type_leaves;
        if(!count_type_leaves(target_type, target_type_leaves) &&
           target_type_leaves>0)
        {
          dest.insert(dest.end(),
            extract_from.begin()+memory_offset.to_long(),
            extract_from.begin()+(memory_offset+target_type_leaves).to_long());
          return;
        }
      }
    }
  }
  else if(expr.id()==ID_dereference ||
          expr.id()==ID_index ||
          expr.id()==ID_symbol ||
          expr.id()==ID_member)
  {
    mp_integer address=evaluate_address(
      expr,
      true); // fail quietly
    if(address.is_zero())
    {
      exprt simplified;
      // In case of being an indexed access, try to evaluate the index, then
      // simplify.
      if(expr.id() == ID_index)
      {
        auto const &index_expr = to_index_expr(expr);
        index_exprt evaluated_index = index_expr;
        mp_vectort index;
        evaluate(index_expr.index(), index);
        if(index.size() == 1)
        {
          evaluated_index.index() =
            constant_exprt(integer2string(index[0]), index_expr.index().type());
        }
        simplified = simplify_expr(evaluated_index, ns);
      }
      else
      {
        // Try reading from a constant -- simplify_expr has all the relevant
        // cases (index-of-constant-array, member-of-constant-struct and so on)
        // Note we complain of a problem even if simplify did *something* but
        // still left us with an unresolved index, member, etc.
        simplified = simplify_expr(expr, ns);
      }
      if(simplified.id() == expr.id())
        evaluate_address(expr); // Evaluate again to print error message.
      else
      {
        evaluate(simplified, dest);
        return;
      }
    }
    else if(!address.is_zero())
    {
      if(!unbounded_size(expr.type()))
      {
        dest.resize(integer2size_t(get_size(expr.type())));
        read(address, dest);
      }
      else
      {
        read_unbounded(address, dest);
      }
      return;
    }
  }
  else if(expr.id()==ID_typecast)
  {
    auto const &typecast_expr = to_typecast_expr(expr);

    mp_vectort casted;
    evaluate(typecast_expr.op(), casted);

    if(casted.size() == 1)
    {
      const mp_integer &value = casted.front();

      if(typecast_expr.type().id() == ID_pointer)
      {
        dest.push_back(value);
        return;
      }
      else if(typecast_expr.type().id() == ID_signedbv)
      {
        const std::string s =
          integer2bv(value, to_signedbv_type(typecast_expr.type()).get_width());
        dest.push_back(bv2integer(s, true));
        return;
      }
      else if(typecast_expr.type().id() == ID_unsignedbv)
      {
        const std::string s = integer2bv(
          value, to_unsignedbv_type(typecast_expr.type()).get_width());
        dest.push_back(bv2integer(s, false));
        return;
      }
      else if(
        (typecast_expr.type().id() == ID_bool) ||
        (typecast_expr.type().id() == ID_c_bool))
      {
        dest.push_back(value!=0);
        return;
      }
    }
  }
  else if(expr.id()==ID_array)
  {
    auto const &array_expr = to_array_expr(expr);
    forall_operands(it, array_expr)
    {
      evaluate(*it, dest);
    }
    return;
  }
  else if(expr.id()==ID_array_of)
  {
    auto const &array_of_expr = to_array_of_expr(expr);
    const auto &array_of_type = to_array_type(array_of_expr.type());
    std::vector<mp_integer> size;
    if(array_of_type.size().id() == ID_infinity)
      size.push_back(0);
    else
      evaluate(array_of_type.size(), size);

    if(size.size()==1)
    {
      std::size_t size_int=integer2size_t(size[0]);
      for(std::size_t i=0; i<size_int; ++i)
        evaluate(array_of_expr.what(), dest);
      return;
    }
  }
  else if(expr.id()==ID_with)
  {
    const auto &wexpr=to_with_expr(expr);
    evaluate(wexpr.old(), dest);
    std::vector<mp_integer> where;
    std::vector<mp_integer> new_value;
    evaluate(wexpr.where(), where);
    evaluate(wexpr.new_value(), new_value);
    const auto &subtype=expr.type().subtype();
    if(!new_value.empty() && where.size()==1 && !unbounded_size(subtype))
    {
      // Ignore indices < 0, which the string solver sometimes produces
      if(where[0]<0)
        return;

      mp_integer where_idx=where[0];
      mp_integer subtype_size=get_size(subtype);
      mp_integer need_size=(where_idx+1)*subtype_size;

      if(dest.size()<need_size)
        dest.resize(integer2size_t(need_size), 0);

      for(std::size_t i=0; i<new_value.size(); ++i)
        dest[integer2size_t((where_idx*subtype_size)+i)]=new_value[i];

      return;
    }
  }
  else if(expr.id()==ID_nil)
  {
    dest.push_back(0);
    return;
  }
  else if(expr.id()==ID_infinity)
  {
    if(expr.type().id()==ID_signedbv)
    {
      warning() << "Infinite size arrays not supported" << eom;
      return;
    }
  }
  error() << "!! failed to evaluate expression: "
          << from_expr(ns, function->first, expr) << "\n"
          << expr.id() << "[" << expr.type().id() << "]"
          << eom;
}

mp_integer interpretert::evaluate_address(
  const exprt &expr,
  bool fail_quietly)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier = is_ssa_expr(expr)
                                   ? to_ssa_expr(expr).get_original_name()
                                   : to_symbol_expr(expr).get_identifier();

    interpretert::memory_mapt::const_iterator m_it1=
      memory_map.find(identifier);

    if(m_it1!=memory_map.end())
      return m_it1->second;

    if(!call_stack.empty())
    {
      interpretert::memory_mapt::const_iterator m_it2=
        call_stack.top().local_map.find(identifier);

      if(m_it2!=call_stack.top().local_map.end())
        return m_it2->second;
    }
    mp_integer address=memory.size();
    build_memory_map(to_symbol_expr(expr).get_identifier(), expr.type());
    return address;
  }
  else if(expr.id()==ID_dereference)
  {
    auto const &dereference_expr = to_dereference_expr(expr);

    mp_vectort pointer;
    evaluate(dereference_expr.pointer(), pointer);

    if(pointer.size() == 1)
      return pointer.front();
  }
  else if(expr.id()==ID_index)
  {
    auto const &index_expr = to_index_expr(expr);

    mp_vectort index;
    evaluate(index_expr.index(), index);

    if(index.size() == 1)
    {
      auto base = evaluate_address(index_expr.array(), fail_quietly);
      if(!base.is_zero())
        return base + index.front();
    }
  }
  else if(expr.id()==ID_member)
  {
    auto const &member_expr = to_member_expr(expr);

    const struct_typet &struct_type =
      to_struct_type(ns.follow(member_expr.compound().type()));

    const irep_idt &component_name = member_expr.get_component_name();

    mp_integer offset=0;

    for(const auto &comp : struct_type.components())
    {
      if(comp.get_name()==component_name)
        break;

      offset+=get_size(comp.type());
    }

    auto base = evaluate_address(member_expr.compound(), fail_quietly);
    if(!base.is_zero())
      return base+offset;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    auto const &byte_extract_expr = to_byte_extract_expr(expr);
    mp_vectort extract_offset;
    evaluate(byte_extract_expr.offset(), extract_offset);
    mp_vectort extract_from;
    evaluate(byte_extract_expr.op(), extract_from);
    if(extract_offset.size()==1 && !extract_from.empty())
    {
      mp_integer memory_offset;
      if(!byte_offset_to_memory_offset(
           byte_extract_expr.op().type(), extract_offset[0], memory_offset))
      {
        return evaluate_address(byte_extract_expr.op(), fail_quietly) +
               memory_offset;
      }
    }
  }
  else if(expr.id()==ID_if)
  {
    auto const &if_expr = to_if_expr(expr);
    mp_vectort result;
    if_exprt address_cond(
      if_expr.cond(),
      address_of_exprt(if_expr.true_case()),
      address_of_exprt(if_expr.false_case()));
    evaluate(address_cond, result);
    if(result.size()==1)
      return result[0];
  }
  else if(expr.id()==ID_typecast)
  {
    auto const &typecast_expr = to_typecast_expr(expr);
    return evaluate_address(typecast_expr.op(), fail_quietly);
  }
  if(!fail_quietly)
  {
    error() << "!! failed to evaluate address: "
            << from_expr(ns, function->first, expr)
            << eom;
  }

  return 0;
}
