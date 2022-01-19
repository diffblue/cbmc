/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#include "interpreter_class.h"

#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/ssa_expr.h>
#include <util/std_code.h>
#include <util/string_container.h>

#include <langapi/language_util.h>
#include <util/expr_util.h>

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
      const memory_cellt &cell =
        memory[numeric_cast_v<std::size_t>(address + i)];
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
  std::size_t address_val = numeric_cast_v<std::size_t>(address);
  const mp_integer offset=address_to_offset(address_val);
  const mp_integer alloc_size=
    base_address_to_actual_size(address_val-offset);
  const mp_integer to_read=alloc_size-offset;
  for(size_t i=0; i<to_read; i++)
  {
    mp_integer value;

    if((address+i)<memory.size())
    {
      const memory_cellt &cell =
        memory[numeric_cast_v<std::size_t>(address + i)];
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
      memory_cellt &cell = memory[numeric_cast_v<std::size_t>(address + i)];
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
    mp_vectort array_size_vec = evaluate(at.size());
    if(array_size_vec.size()!=1)
      return true;
    mp_integer subtype_count;
    if(count_type_leaves(at.element_type(), subtype_count))
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

    mp_vectort array_size_vec = evaluate(at.size());

    if(array_size_vec.size()!=1)
      return true;

    mp_integer array_size=array_size_vec[0];
    auto elem_size_bytes = pointer_offset_size(at.element_type(), ns);
    if(!elem_size_bytes.has_value() || *elem_size_bytes == 0)
      return true;

    mp_integer elem_size_leaves;
    if(count_type_leaves(at.element_type(), elem_size_leaves))
      return true;

    mp_integer this_idx = offset / (*elem_size_bytes);
    if(this_idx>=array_size_vec[0])
      return true;

    mp_integer subtype_result;
    bool ret = byte_offset_to_memory_offset(
      at.element_type(), offset % (*elem_size_bytes), subtype_result);

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

    mp_vectort array_size_vec = evaluate(at.size());
    if(array_size_vec.size()!=1)
      return true;

    auto elem_size = pointer_offset_size(at.element_type(), ns);
    if(!elem_size.has_value())
      return true;

    mp_integer elem_count;
    if(count_type_leaves(at.element_type(), elem_count))
      return true;

    mp_integer this_idx=full_cell_offset/elem_count;
    if(this_idx>=array_size_vec[0])
      return true;

    mp_integer subtype_result;
    bool ret = memory_offset_to_byte_offset(
      at.element_type(), full_cell_offset % elem_count, subtype_result);
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
/// \return vector in which the result of the evaluation is stored
interpretert::mp_vectort interpretert::evaluate(const exprt &expr)
{
  if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_struct)
    {
      mp_vectort dest;
      dest.reserve(numeric_cast_v<std::size_t>(get_size(expr.type())));
      bool error=false;

      forall_operands(it, expr)
      {
        if(it->type().id()==ID_code)
          continue;

        mp_integer sub_size=get_size(it->type());
        if(sub_size==0)
          continue;

        mp_vectort tmp = evaluate(*it);

        if(tmp.size()==sub_size)
        {
          for(std::size_t i=0; i<tmp.size(); ++i)
            dest.push_back(tmp[i]);
        }
        else
          error=true;
      }

      if(!error)
        return dest;

      dest.clear();
    }
    else if(expr.type().id() == ID_pointer)
    {
      if(expr.has_operands())
      {
        const exprt &object = skip_typecast(to_unary_expr(expr).op());
        if(object.id() == ID_address_of)
          return evaluate(object);
        else if(const auto i = numeric_cast<mp_integer>(object))
          return {*i};
      }
      // check if expression is constant null pointer without operands
      else
      {
        const auto i = numeric_cast<mp_integer>(expr);
        if(i && i->is_zero())
          return {*i};
      }
    }
    else if(expr.type().id()==ID_floatbv)
    {
      ieee_floatt f;
      f.from_expr(to_constant_expr(expr));
      return {f.pack()};
    }
    else if(expr.type().id()==ID_fixedbv)
    {
      fixedbvt f;
      f.from_expr(to_constant_expr(expr));
      return {f.get_value()};
    }
    else if(expr.type().id()==ID_c_bool)
    {
      const irep_idt &value=to_constant_expr(expr).get_value();
      const auto width = to_c_bool_type(expr.type()).get_width();
      return {bvrep2integer(value, width, false)};
    }
    else if(expr.type().id()==ID_bool)
    {
      return {expr.is_true()};
    }
    else if(expr.type().id()==ID_string)
    {
      const std::string &value = id2string(to_constant_expr(expr).get_value());
      if(show)
        output.warning() << "string decoding not fully implemented "
                         << value.size() + 1 << messaget::eom;
      return {get_string_container()[value]};
    }
    else
    {
      if(const auto i = numeric_cast<mp_integer>(expr))
        return {*i};
    }
  }
  else if(expr.id()==ID_struct)
  {
    mp_vectort dest;

    if(!unbounded_size(expr.type()))
      dest.reserve(numeric_cast_v<std::size_t>(get_size(expr.type())));

    bool error=false;

    forall_operands(it, expr)
    {
      if(it->type().id()==ID_code)
        continue;

      mp_integer sub_size=get_size(it->type());
      if(sub_size==0)
        continue;

      mp_vectort tmp = evaluate(*it);

      if(unbounded_size(it->type()) || tmp.size()==sub_size)
      {
        for(std::size_t i=0; i<tmp.size(); i++)
          dest.push_back(tmp[i]);
      }
      else
        error=true;
    }

    if(!error)
      return dest;

    dest.clear();
  }
  else if(expr.id()==ID_side_effect)
  {
    side_effect_exprt side_effect=to_side_effect_expr(expr);
    if(side_effect.get_statement()==ID_nondet)
    {
      if(show)
        output.error() << "nondet not implemented" << messaget::eom;
      return {};
    }
    else if(side_effect.get_statement()==ID_allocate)
    {
      if(show)
        output.error() << "heap memory allocation not fully implemented "
                       << expr.type().subtype().pretty() << messaget::eom;
      std::stringstream buffer;
      num_dynamic_objects++;
      buffer << "interpreter::dynamic_object" << num_dynamic_objects;
      irep_idt id(buffer.str().c_str());
      mp_integer address =
        build_memory_map(symbol_exprt{id, expr.type().subtype()});
      // TODO: check array of type
      // TODO: interpret zero-initialization argument
      return {address};
    }
    if(show)
      output.error() << "side effect not implemented "
                     << side_effect.get_statement() << messaget::eom;
  }
  else if(expr.id()==ID_bitor)
  {
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=0;
    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      if(tmp.size()==1)
        final=bitwise_or(final, tmp.front());
    }
    return {final};
  }
  else if(expr.id()==ID_bitand)
  {
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=-1;
    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      if(tmp.size()==1)
        final=bitwise_and(final, tmp.front());
    }

    return {final};
  }
  else if(expr.id()==ID_bitxor)
  {
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=0;
    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      if(tmp.size()==1)
        final=bitwise_xor(final, tmp.front());
    }

    return {final};
  }
  else if(expr.id()==ID_bitnot)
  {
    mp_vectort tmp = evaluate(to_bitnot_expr(expr).op());
    if(tmp.size()==1)
    {
      const auto width =
        to_bitvector_type(to_bitnot_expr(expr).op().type()).get_width();
      const mp_integer mask = power(2, width) - 1;

      return {bitwise_xor(tmp.front(), mask)};
    }
  }
  else if(expr.id()==ID_shl)
  {
    mp_vectort tmp0 = evaluate(to_shl_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_shl_expr(expr).op1());
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final = arith_left_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(to_shl_expr(expr).op0().type()).get_width());
      return {final};
    }
  }
  else if(expr.id() == ID_shr || expr.id() == ID_lshr)
  {
    mp_vectort tmp0 = evaluate(to_shift_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_shift_expr(expr).op1());
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final = logic_right_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(to_shift_expr(expr).op0().type()).get_width());
      return {final};
    }
  }
  else if(expr.id()==ID_ashr)
  {
    mp_vectort tmp0 = evaluate(to_shift_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_shift_expr(expr).op1());
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final = arith_right_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(to_shift_expr(expr).op0().type()).get_width());
      return {final};
    }
  }
  else if(expr.id()==ID_ror)
  {
    mp_vectort tmp0 = evaluate(to_binary_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_binary_expr(expr).op1());
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final = rotate_right(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(to_binary_expr(expr).op0().type()).get_width());
      return {final};
    }
  }
  else if(expr.id()==ID_rol)
  {
    mp_vectort tmp0 = evaluate(to_binary_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_binary_expr(expr).op1());
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final = rotate_left(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(to_binary_expr(expr).op0().type()).get_width());
      return {final};
    }
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_notequal ||
          expr.id()==ID_le ||
          expr.id()==ID_ge ||
          expr.id()==ID_lt ||
          expr.id()==ID_gt)
  {
    mp_vectort tmp0 = evaluate(to_binary_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_binary_expr(expr).op1());

    if(tmp0.size()==1 && tmp1.size()==1)
    {
      const mp_integer &op0=tmp0.front();
      const mp_integer &op1=tmp1.front();

      if(expr.id()==ID_equal)
        return {op0 == op1};
      else if(expr.id()==ID_notequal)
        return {op0 != op1};
      else if(expr.id()==ID_le)
        return {op0 <= op1};
      else if(expr.id()==ID_ge)
        return {op0 >= op1};
      else if(expr.id()==ID_lt)
        return {op0 < op1};
      else if(expr.id()==ID_gt)
        return {op0 > op1};
    }

    return {};
  }
  else if(expr.id()==ID_or)
  {
    if(expr.operands().empty())
      throw id2string(expr.id())+" expects at least one operand";

    bool result=false;

    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);

      if(tmp.size()==1 && tmp.front()!=0)
      {
        result=true;
        break;
      }
    }

    return {result};
  }
  else if(expr.id()==ID_if)
  {
    const auto &if_expr = to_if_expr(expr);

    mp_vectort tmp0 = evaluate(if_expr.cond());
    mp_vectort tmp1;

    if(tmp0.size()==1)
    {
      if(tmp0.front()!=0)
        tmp1 = evaluate(if_expr.true_case());
      else
        tmp1 = evaluate(if_expr.false_case());
    }

    if(tmp1.size()==1)
      return {tmp1.front()};

    return {};
  }
  else if(expr.id()==ID_and)
  {
    if(expr.operands().empty())
      throw id2string(expr.id())+" expects at least one operand";

    bool result=true;

    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);

      if(tmp.size()==1 && tmp.front()==0)
      {
        result=false;
        break;
      }
    }

    return {result};
  }
  else if(expr.id()==ID_not)
  {
    mp_vectort tmp = evaluate(to_not_expr(expr).op());

    if(tmp.size()==1)
      return {tmp.front() == 0};

    return {};
  }
  else if(expr.id()==ID_plus)
  {
    mp_integer result=0;

    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      if(tmp.size()==1)
        result+=tmp.front();
    }

    return {result};
  }
  else if(expr.id()==ID_mult)
  {
    // type-dependent!
    mp_integer result;

    if(expr.type().id()==ID_fixedbv)
    {
      fixedbvt f;
      f.spec=fixedbv_spect(to_fixedbv_type(expr.type()));
      f.from_integer(1);
      result=f.get_value();
    }
    else if(expr.type().id()==ID_floatbv)
    {
      ieee_floatt f(to_floatbv_type(expr.type()));
      f.from_integer(1);
      result=f.pack();
    }
    else
      result=1;

    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      if(tmp.size()==1)
      {
        if(expr.type().id()==ID_fixedbv)
        {
          fixedbvt f1, f2;
          f1.spec=fixedbv_spect(to_fixedbv_type(expr.type()));
          f2.spec=fixedbv_spect(to_fixedbv_type(it->type()));
          f1.set_value(result);
          f2.set_value(tmp.front());
          f1*=f2;
          result=f1.get_value();
        }
        else if(expr.type().id()==ID_floatbv)
        {
          ieee_floatt f1(to_floatbv_type(expr.type()));
          ieee_floatt f2(to_floatbv_type(it->type()));
          f1.unpack(result);
          f2.unpack(tmp.front());
          f1*=f2;
          result=f2.pack();
        }
        else
          result*=tmp.front();
      }
    }

    return {result};
  }
  else if(expr.id()==ID_minus)
  {
    mp_vectort tmp0 = evaluate(to_minus_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_minus_expr(expr).op1());

    if(tmp0.size()==1 && tmp1.size()==1)
      return {tmp0.front() - tmp1.front()};
    return {};
  }
  else if(expr.id()==ID_div)
  {
    mp_vectort tmp0 = evaluate(to_div_expr(expr).op0());
    mp_vectort tmp1 = evaluate(to_div_expr(expr).op1());

    if(tmp0.size()==1 && tmp1.size()==1)
      return {tmp0.front() / tmp1.front()};
    return {};
  }
  else if(expr.id()==ID_unary_minus)
  {
    mp_vectort tmp0 = evaluate(to_unary_minus_expr(expr).op());

    if(tmp0.size()==1)
      return {-tmp0.front()};
    return {};
  }
  else if(expr.id()==ID_address_of)
  {
    return {evaluate_address(to_address_of_expr(expr).op())};
  }
  else if(expr.id()==ID_pointer_offset)
  {
    if(expr.operands().size()!=1)
      throw "pointer_offset expects one operand";

    if(to_unary_expr(expr).op().type().id() != ID_pointer)
      throw "pointer_offset expects a pointer operand";

    mp_vectort result = evaluate(to_unary_expr(expr).op());

    if(result.size()==1)
    {
      // Return the distance, in bytes, between the address returned
      // and the beginning of the underlying object.
      mp_integer address=result[0];
      if(address>0 && address<memory.size())
      {
        auto obj_type = address_to_symbol(address).type();

        mp_integer offset=address_to_offset(address);
        mp_integer byte_offset;
        if(!memory_offset_to_byte_offset(obj_type, offset, byte_offset))
          return {byte_offset};
      }
    }
    return {};
  }
  else if(
    expr.id() == ID_dereference || expr.id() == ID_index ||
    expr.id() == ID_symbol || expr.id() == ID_member ||
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
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
        index_exprt evaluated_index = to_index_expr(expr);
        mp_vectort idx = evaluate(to_index_expr(expr).index());
        if(idx.size() == 1)
        {
          evaluated_index.index() =
            from_integer(idx[0], to_index_expr(expr).index().type());
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
        return evaluate(simplified);
    }
    else if(!address.is_zero())
    {
      if(
        expr.id() == ID_byte_extract_little_endian ||
        expr.id() == ID_byte_extract_big_endian)
      {
        const auto &byte_extract_expr = to_byte_extract_expr(expr);

        mp_vectort extract_from = evaluate(byte_extract_expr.op());
        INVARIANT(
          !extract_from.empty(),
          "evaluate_address should have returned address == 0");
        const mp_integer memory_offset =
          address - evaluate_address(byte_extract_expr.op(), true);
        const typet &target_type = expr.type();
        mp_integer target_type_leaves;
        if(
          !count_type_leaves(target_type, target_type_leaves) &&
          target_type_leaves > 0)
        {
          mp_vectort dest;
          dest.insert(
            dest.end(),
            extract_from.begin() + numeric_cast_v<std::size_t>(memory_offset),
            extract_from.begin() +
              numeric_cast_v<std::size_t>(memory_offset + target_type_leaves));
          return dest;
        }
        // we fail
      }
      else if(!unbounded_size(expr.type()))
      {
        mp_vectort dest;
        dest.resize(numeric_cast_v<std::size_t>(get_size(expr.type())));
        read(address, dest);
        return dest;
      }
      else
      {
        mp_vectort dest;
        read_unbounded(address, dest);
        return dest;
      }
    }
  }
  else if(expr.id()==ID_typecast)
  {
    mp_vectort tmp = evaluate(to_typecast_expr(expr).op());

    if(tmp.size()==1)
    {
      const mp_integer &value=tmp.front();

      if(expr.type().id()==ID_pointer)
      {
        return {value};
      }
      else if(expr.type().id()==ID_signedbv)
      {
        const auto width = to_signedbv_type(expr.type()).get_width();
        const auto s = integer2bvrep(value, width);
        return {bvrep2integer(s, width, true)};
      }
      else if(expr.type().id()==ID_unsignedbv)
      {
        const auto width = to_unsignedbv_type(expr.type()).get_width();
        const auto s = integer2bvrep(value, width);
        return {bvrep2integer(s, width, false)};
      }
      else if((expr.type().id()==ID_bool) || (expr.type().id()==ID_c_bool))
        return {value != 0};
    }
  }
  else if(expr.id()==ID_array)
  {
    mp_vectort dest;
    forall_operands(it, expr)
    {
      mp_vectort tmp = evaluate(*it);
      dest.insert(dest.end(), tmp.begin(), tmp.end());
    }
    return dest;
  }
  else if(expr.id()==ID_array_of)
  {
    const auto &ty=to_array_type(expr.type());

    mp_vectort size;
    if(ty.size().id()==ID_infinity)
      size.push_back(0);
    else
      size = evaluate(ty.size());

    if(size.size()==1)
    {
      std::size_t size_int = numeric_cast_v<std::size_t>(size[0]);
      mp_vectort tmp = evaluate(to_array_of_expr(expr).op());
      mp_vectort dest;
      for(std::size_t i=0; i<size_int; ++i)
        dest.insert(dest.end(), tmp.begin(), tmp.end());
      return dest;
    }
  }
  else if(expr.id()==ID_with)
  {
    const auto &wexpr=to_with_expr(expr);

    mp_vectort dest = evaluate(wexpr.old());
    mp_vectort where = evaluate(wexpr.where());
    mp_vectort new_value = evaluate(wexpr.new_value());

    const auto &subtype=expr.type().subtype();

    if(!new_value.empty() && where.size()==1 && !unbounded_size(subtype))
    {
      // Ignore indices < 0, which the string solver sometimes produces
      if(where[0]<0)
        return {};

      mp_integer where_idx=where[0];
      mp_integer subtype_size=get_size(subtype);
      mp_integer need_size=(where_idx+1)*subtype_size;

      if(dest.size()<need_size)
        dest.resize(numeric_cast_v<std::size_t>(need_size), 0);

      for(std::size_t i=0; i<new_value.size(); ++i)
        dest[numeric_cast_v<std::size_t>((where_idx * subtype_size) + i)] =
          new_value[i];

      return {};
    }
  }
  else if(expr.id()==ID_nil)
  {
    return {0};
  }
  else if(expr.id()==ID_infinity)
  {
    if(expr.type().id()==ID_signedbv)
    {
      output.warning() << "Infinite size arrays not supported" << messaget::eom;
      return {};
    }
  }
  output.error() << "!! failed to evaluate expression: "
                 << from_expr(ns, function->first, expr) << "\n"
                 << expr.id() << "[" << expr.type().id() << "]"
                 << messaget::eom;
  return {};
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
    build_memory_map(to_symbol_expr(expr));
    return address;
  }
  else if(expr.id()==ID_dereference)
  {
    mp_vectort tmp0 = evaluate(to_dereference_expr(expr).op());

    if(tmp0.size()==1)
      return tmp0.front();
  }
  else if(expr.id()==ID_index)
  {
    mp_vectort tmp1 = evaluate(to_index_expr(expr).index());

    if(tmp1.size()==1)
    {
      auto base = evaluate_address(to_index_expr(expr).array(), fail_quietly);
      if(!base.is_zero())
        return base+tmp1.front();
    }
  }
  else if(expr.id()==ID_member)
  {
    const struct_typet &struct_type =
      to_struct_type(ns.follow(to_member_expr(expr).compound().type()));

    const irep_idt &component_name=
      to_member_expr(expr).get_component_name();

    mp_integer offset=0;

    for(const auto &comp : struct_type.components())
    {
      if(comp.get_name()==component_name)
        break;

      offset+=get_size(comp.type());
    }

    auto base = evaluate_address(to_member_expr(expr).compound(), fail_quietly);
    if(!base.is_zero())
      return base+offset;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr = to_byte_extract_expr(expr);
    mp_vectort extract_offset = evaluate(byte_extract_expr.op1());
    mp_vectort extract_from = evaluate(byte_extract_expr.op0());
    if(extract_offset.size()==1 && !extract_from.empty())
    {
      mp_integer memory_offset;
      if(!byte_offset_to_memory_offset(
           byte_extract_expr.op0().type(), extract_offset[0], memory_offset))
        return evaluate_address(byte_extract_expr.op0(), fail_quietly) +
               memory_offset;
    }
  }
  else if(expr.id()==ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    if_exprt address_cond(
      if_expr.cond(),
      address_of_exprt(if_expr.true_case()),
      address_of_exprt(if_expr.false_case()));
    mp_vectort result = evaluate(address_cond);
    if(result.size()==1)
      return {result[0]};
  }
  else if(expr.id()==ID_typecast)
  {
    return evaluate_address(to_typecast_expr(expr).op(), fail_quietly);
  }

  if(!fail_quietly)
  {
    output.error() << "!! failed to evaluate address: "
                   << from_expr(ns, function->first, expr) << messaget::eom;
  }

  return 0;
}
