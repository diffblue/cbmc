/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#include "interpreter_class.h"

#include <cassert>
#include <iostream>
#include <sstream>

#include <util/ieee_float.h>
#include <util/fixedbv.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>
#include <string.h>

/// reads a memory address and loads it into the dest variable marks cell as
/// read before written if cell has never been written
void interpretert::read(
  mp_integer address,
  mp_vectort &dest) const
{
  // copy memory region
  for(size_t i=0; i<dest.size(); i++)
  {
    mp_integer value;

    if((address+i)<memory.size())
    {
      const memory_cellt &cell=memory[integer2size_t(address+i)];
      value=cell.value;
      if(cell.initialized==0)
        cell.initialized=-1;
    }
    else
      value=0;

    dest[i]=value;
  }
}

void interpretert::read_unbounded(
  mp_integer address,
  mp_vectort &dest) const
{
  // copy memory region
  std::size_t address_val=integer2size_t(address);
  const std::size_t offset=address_to_offset(address_val);
  const std::size_t alloc_size=
    base_address_to_actual_size(address_val-offset);
  const std::size_t to_read=alloc_size-offset;
  for(size_t i=0; i<to_read; i++)
  {
    mp_integer value;

    if((address+i)<memory.size())
    {
      const memory_cellt &cell=memory[integer2size_t(address+i)];
      value=cell.value;
      if(cell.initialized==0)
        cell.initialized=-1;
    }
    else
      value=0;

    dest.push_back(value);
  }
}

/// reserves memory block of size at address
void interpretert::allocate(
  mp_integer address,
  size_t size)
{
  // clear memory region
  for(size_t i=0; i<size; i++)
  {
    if((address+i)<memory.size())
    {
      memory_cellt &cell=memory[integer2size_t(address+i)];
      cell.value=0;
      cell.initialized=0;
    }
  }
}

/// Clears memoy r/w flag initialization
void interpretert::clear_input_flags()
{
  for(const memory_cellt &cell : memory)
  {
    if(cell.initialized>0)
      cell.initialized=0;
  }
}

/// \return Number of leaf primitive types; returns true on error
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
  mp_integer offset,
  mp_integer &result)
{
  if(source_type.id()==ID_struct)
  {
    const auto &st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator component_offsets(st, ns);
    mp_integer previous_member_offsets=0;
    for(; component_offsets->first<components.size() &&
          component_offsets->second!=-1 &&
          component_offsets->second<=offset;
          ++component_offsets)
    {
      const auto &component_type=components[component_offsets->first].type();
      mp_integer component_byte_size=pointer_offset_size(component_type, ns);
      if(component_byte_size<0)
        return true;
      if((component_offsets->second+component_byte_size)>offset)
      {
        mp_integer subtype_result;
        bool ret=byte_offset_to_memory_offset(
          component_type,
          offset-(component_offsets->second),
          subtype_result);
        result=previous_member_offsets+subtype_result;
        return ret;
      }
      else
      {
        mp_integer component_count;
        if(count_type_leaves(component_type, component_count))
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
    mp_integer elem_size_bytes=pointer_offset_size(at.subtype(), ns);
    if(elem_size_bytes<=0)
      return true;
    mp_integer elem_size_leaves;
    if(count_type_leaves(at.subtype(), elem_size_leaves))
      return true;
    mp_integer this_idx=offset/elem_size_bytes;
    if(this_idx>=array_size_vec[0])
      return true;
    mp_integer subtype_result;
    bool ret=byte_offset_to_memory_offset(
      at.subtype(),
      offset%elem_size_bytes,
      subtype_result);
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
  mp_integer cell_offset,
  mp_integer &result)
{
  if(source_type.id()==ID_struct)
  {
    const auto &st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator offsets(st, ns);
    mp_integer previous_member_sizes;
    for(; offsets->first<components.size() && offsets->second!=-1; ++offsets)
    {
      const auto &component_type=components[offsets->first].type();
      mp_integer component_count;
      if(count_type_leaves(component_type, component_count))
        return true;
      if(component_count>cell_offset)
      {
        mp_integer subtype_result;
        bool ret=memory_offset_to_byte_offset(
          component_type,
          cell_offset,
          subtype_result);
        result=previous_member_sizes+subtype_result;
        return ret;
      }
      else
      {
        cell_offset-=component_count;
        mp_integer component_size=pointer_offset_size(component_type, ns);
        if(component_size<0)
          return true;
        previous_member_sizes+=component_size;
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
    mp_integer elem_size=pointer_offset_size(at.subtype(), ns);
    if(elem_size==-1)
      return true;
    mp_integer elem_count;
    if(count_type_leaves(at.subtype(), elem_count))
      return true;
    mp_integer this_idx=cell_offset/elem_count;
    if(this_idx>=array_size_vec[0])
      return true;
    mp_integer subtype_result;
    bool ret=
      memory_offset_to_byte_offset(at.subtype(),
        cell_offset%elem_count,
        subtype_result);
    result=subtype_result+(elem_size*this_idx);
    return ret;
  }
  else
  {
    // Primitive type.
    result=0;
    return cell_offset!=0;
  }
}

void interpretert::evaluate(
  const exprt &expr,
  mp_vectort &dest)
{
  if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_struct)
    {
      dest.reserve(get_size(expr.type()));
      bool error=false;

      forall_operands(it, expr)
      {
        if(it->type().id()==ID_code)
          continue;

        size_t sub_size=get_size(it->type());
        if(sub_size==0)
          continue;

        mp_vectort tmp;
        evaluate(*it, tmp);

        if(tmp.size()==sub_size)
        {
          for(size_t i=0; i<sub_size; i++)
            dest.push_back(tmp[i]);
        }
        else
          error=true;
      }

      if(!error)
        return;

      dest.clear();
    }
    else if((expr.type().id()==ID_pointer)
         || (expr.type().id()==ID_address_of))
    {
      mp_integer i=0;
      if(expr.has_operands() && expr.op0().id()==ID_address_of)
      {
        evaluate(expr.op0(), dest);
        return;
      }
      if(expr.has_operands() && !to_integer(expr.op0(), i))
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
      dest.push_back(binary2integer(id2string(value), false));
      return;
    }
    else if(expr.type().id()==ID_bool)
    {
      dest.push_back(expr.is_true());
      return;
    }
    else if(expr.type().id()==ID_string)
    {
      irep_idt value=to_constant_expr(expr).get_value();
      const char *str=value.c_str();
      size_t length=strlen(str)+1;
      if(show)
        warning() << "string decoding not fully implemented "
                  << length << eom;
      mp_integer tmp=value.get_no();
      dest.push_back(tmp);
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
    dest.reserve(get_size(expr.type()));
    bool error=false;

    forall_operands(it, expr)
    {
      if(it->type().id()==ID_code)
        continue;

      size_t sub_size=get_size(it->type());
      if(sub_size==0)
        continue;

      mp_vectort tmp;
      evaluate(*it, tmp);

      if(tmp.size()==sub_size)
      {
        for(size_t i=0; i<sub_size; i++)
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
    else if(side_effect.get_statement()==ID_malloc)
    {
      if(show)
        error() << "malloc not fully implemented "
                << expr.type().subtype().pretty()
                << eom;
      std::stringstream buffer;
      num_dynamic_objects++;
      buffer << "interpreter::malloc_object" << num_dynamic_objects;
      irep_idt id(buffer.str().c_str());
      mp_integer address=build_memory_map(id, expr.type().subtype());
      // TODO: check array of type
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
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=0;
    forall_operands(it, expr)
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
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=-1;
    forall_operands(it, expr)
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
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=0;
    forall_operands(it, expr)
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
    if(expr.operands().size()!=1)
      throw id2string(expr.id())+" expects one operand";
    mp_vectort tmp;
    evaluate(expr.op0(), tmp);
    if(tmp.size()==1)
    {
      dest.push_back(bitwise_neg(tmp.front()));
      return;
    }
  }
  else if(expr.id()==ID_shl)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=arith_left_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(expr.op0().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if((expr.id()==ID_shr) || (expr.id()==ID_lshr))
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=logic_right_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(expr.op0().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_ashr)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=arith_right_shift(
        tmp0.front(),
        tmp1.front(),
        to_bitvector_type(expr.op0().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_ror)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=rotate_right(tmp0.front(),
        tmp1.front(),
        to_bitvector_type(expr.op0().type()).get_width());
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_rol)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=rotate_left(tmp0.front(),
        tmp1.front(),
        to_bitvector_type(expr.op0().type()).get_width());
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
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);

    if(tmp0.size()==1 && tmp1.size()==1)
    {
      const mp_integer &op0=tmp0.front();
      const mp_integer &op1=tmp1.front();

      if(expr.id()==ID_equal)
        dest.push_back(op0==op1);
      else if(expr.id()==ID_notequal)
        dest.push_back(op0!=op1);
      else if(expr.id()==ID_le)
        dest.push_back(op0<=op1);
      else if(expr.id()==ID_ge)
        dest.push_back(op0>=op1);
      else if(expr.id()==ID_lt)
        dest.push_back(op0<op1);
      else if(expr.id()==ID_gt)
        dest.push_back(op0>op1);
    }

    return;
  }
  else if(expr.id()==ID_or)
  {
    if(expr.operands().empty())
      throw id2string(expr.id())+" expects at least one operand";

    bool result=false;

    forall_operands(it, expr)
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
    if(expr.operands().size()!=3)
      throw "if expects three operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);

    if(tmp0.size()==1)
    {
      if(tmp0.front()!=0)
        evaluate(expr.op1(), tmp1);
      else
        evaluate(expr.op2(), tmp1);
    }

    if(tmp1.size()==1)
      dest.push_back(tmp1.front());

    return;
  }
  else if(expr.id()==ID_and)
  {
    if(expr.operands().empty())
      throw id2string(expr.id())+" expects at least one operand";

    bool result=true;

    forall_operands(it, expr)
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
    if(expr.operands().size()!=1)
      throw id2string(expr.id())+" expects one operand";

    mp_vectort tmp;
    evaluate(expr.op0(), tmp);

    if(tmp.size()==1)
      dest.push_back(tmp.front()==0);

    return;
  }
  else if(expr.id()==ID_plus)
  {
    mp_integer result=0;

    forall_operands(it, expr)
    {
      mp_vectort tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1)
        result+=tmp.front();
    }

    dest.push_back(result);
    return;
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
      mp_vectort tmp;
      evaluate(*it, tmp);
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

    dest.push_back(result);
    return;
  }
  else if(expr.id()==ID_minus)
  {
    if(expr.operands().size()!=2)
      throw "- expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);

    if(tmp0.size()==1 && tmp1.size()==1)
      dest.push_back(tmp0.front()-tmp1.front());
    return;
  }
  else if(expr.id()==ID_div)
  {
    if(expr.operands().size()!=2)
      throw "/ expects two operands";

    mp_vectort tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);

    if(tmp0.size()==1 && tmp1.size()==1)
      dest.push_back(tmp0.front()/tmp1.front());
    return;
  }
  else if(expr.id()==ID_unary_minus)
  {
    if(expr.operands().size()!=1)
      throw "unary- expects one operand";

    mp_vectort tmp0;
    evaluate(expr.op0(), tmp0);

    if(tmp0.size()==1)
      dest.push_back(-tmp0.front());
    return;
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw "address_of expects one operand";

    dest.push_back(evaluate_address(expr.op0()));
    return;
  }
  else if(expr.id()==ID_pointer_offset)
  {
    if(expr.operands().size()!=1)
      throw "pointer_offset expects one operand";
    if(expr.op0().type().id()!=ID_pointer)
      throw "pointer_offset expects a pointer operand";
    mp_vectort result;
    evaluate(expr.op0(), result);
    if(result.size()==1)
    {
      // Return the distance, in bytes, between the address returned
      // and the beginning of the underlying object.
      mp_integer address=result[0];
      if(address>0 && address<memory.size())
      {
        const auto &memory_record=memory[integer2unsigned(address)];
        auto obj_type=get_type(memory_record.identifier);

        mp_integer offset=memory_record.offset;
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
    if(expr.operands().size()!=2)
      throw "byte_extract should have two operands";
    mp_vectort extract_offset;
    evaluate(expr.op1(), extract_offset);
    mp_vectort extract_from;
    evaluate(expr.op0(), extract_from);
    if(extract_offset.size()==1 && extract_from.size()!=0)
    {
      const typet &target_type=expr.type();
      mp_integer memory_offset;
      // If memory offset is found (which should normally be the case)
      // extract the corresponding data from the appropriate memory location
      if(!byte_offset_to_memory_offset(
           expr.op0().type(),
           extract_offset[0],
           memory_offset))
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
    if(address.is_zero() && expr.id()==ID_index)
    {
      // Try reading from a constant array:
      mp_vectort idx;
      evaluate(expr.op1(), idx);
      if(idx.size()==1)
      {
        mp_integer read_from_index=idx[0];
        if(expr.op0().id()==ID_array)
        {
          const auto &ops=expr.op0().operands();
          assert(read_from_index.is_long());
          if(read_from_index>=0 && read_from_index<ops.size())
          {
            evaluate(ops[read_from_index.to_long()], dest);
            if(dest.size()!=0)
              return;
          }
        }
        else if(expr.op0().id()=="array-list")
        {
          // This sort of construct comes from boolbv_get, but doesn't seem
          // to have an exprt yet. Its operands are a list of key-value pairs.
          const auto &ops=expr.op0().operands();
          assert(ops.size()%2==0);
          for(size_t listidx=0; listidx!=ops.size(); listidx+=2)
          {
            mp_vectort elem_idx;
            evaluate(ops[listidx], elem_idx);
            assert(elem_idx.size()==1);
            if(elem_idx[0]==read_from_index)
            {
              evaluate(ops[listidx+1], dest);
              if(dest.size()!=0)
                return;
              else
                break;
            }
          }
          // If we fall out the end of this loop then the constant array-list
          // didn't define an element matching the index we're looking for.
        }
      }
      evaluate_address(expr); // Evaluate again to print error message.
    }
    else if(!address.is_zero())
    {
      dest.resize(get_size(expr.type()));
      read(address, dest);
      return;
    }
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast expects one operand";

    mp_vectort tmp;
    evaluate(expr.op0(), tmp);

    if(tmp.size()==1)
    {
      const mp_integer &value=tmp.front();

      if(expr.type().id()==ID_pointer)
      {
        dest.push_back(value);
        return;
      }
      else if(expr.type().id()==ID_signedbv)
      {
        const std::string s=
          integer2binary(value, to_signedbv_type(expr.type()).get_width());
        dest.push_back(binary2integer(s, true));
        return;
      }
      else if(expr.type().id()==ID_unsignedbv)
      {
        const std::string s=
          integer2binary(value, to_unsignedbv_type(expr.type()).get_width());
        dest.push_back(binary2integer(s, false));
        return;
      }
      else if((expr.type().id()==ID_bool) || (expr.type().id()==ID_c_bool))
      {
        dest.push_back(value!=0);
        return;
      }
    }
  }
  else if((expr.id()==ID_array) || (expr.id()==ID_array_of))
  {
    forall_operands(it, expr)
    {
      evaluate(*it, dest);
    }
    return;
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
      error() << "Infinite size arrays not supported" << eom;
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
    const irep_idt &identifier=
      is_ssa_expr(expr) ?
      to_ssa_expr(expr).get_original_name() :
      expr.get(ID_identifier);

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
    if(expr.operands().size()!=1)
      throw "dereference expects one operand";

    mp_vectort tmp0;
    evaluate(expr.op0(), tmp0);

    if(tmp0.size()==1)
      return tmp0.front();
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expects two operands";

    mp_vectort tmp1;
    evaluate(expr.op1(), tmp1);

    if(tmp1.size()==1)
    {
      auto base=evaluate_address(expr.op0(), fail_quietly);
      if(!base.is_zero())
        return base+tmp1.front();
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()!=1)
      throw "member expects one operand";

    const struct_typet &struct_type=
      to_struct_type(ns.follow(expr.op0().type()));

    const irep_idt &component_name=
      to_member_expr(expr).get_component_name();

    unsigned offset=0;

    for(const auto &comp : struct_type.components())
    {
      if(comp.get_name()==component_name)
        break;

      offset+=get_size(comp.type());
    }

    auto base=evaluate_address(expr.op0(), fail_quietly);
    if(!base.is_zero())
      return base+offset;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    if(expr.operands().size()!=2)
      throw "byte_extract should have two operands";
    mp_vectort extract_offset;
    evaluate(expr.op1(), extract_offset);
    mp_vectort extract_from;
    evaluate(expr.op0(), extract_from);
    if(extract_offset.size()==1 && !extract_from.empty())
    {
      mp_integer memory_offset;
      if(!byte_offset_to_memory_offset(expr.op0().type(),
        extract_offset[0], memory_offset))
        return evaluate_address(expr.op0(), fail_quietly)+memory_offset;
    }
  }
  else if(expr.id()==ID_if)
  {
    mp_vectort result;
    if_exprt address_cond(
      expr.op0(),
      address_of_exprt(expr.op1()),
      address_of_exprt(expr.op2()));
    evaluate(address_cond, result);
    if(result.size()==1)
      return result[0];
  }
  if(!fail_quietly)
  {
    error() << "!! failed to evaluate address: "
            << from_expr(ns, function->first, expr)
            << eom;
  }

  return 0;
}
