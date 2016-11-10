/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <sstream>

#include <util/ieee_float.h>
#include <util/fixedbv.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>
#include <string.h>

#include "interpreter_class.h"

/*******************************************************************\

Function: interpretert::read

  Inputs:

 Outputs:

 Purpose: reads a memory address and loads it into the dest variable
          marks cell as read before written if cell has never been written

\*******************************************************************/

void interpretert::read(
  mp_integer address,
  std::vector<mp_integer> &dest) const
{
  // copy memory region
  for(unsigned i=0; i<dest.size(); i++, ++address)
  {
    mp_integer value;
    
    if(address<memory.size()) {
      const memory_cellt &cell=memory[integer2size_t(address)];
      value=cell.value;
      if (cell.initialised==0) cell.initialised=-1;
    }
    else
      value=0;
      
    dest[i]=value;
  }
}

/*******************************************************************\

Function: interpretert::allocate

  Inputs:

 Outputs:

 Purpose: reserves memory block of size at address

\*******************************************************************/

void interpretert::allocate(
  mp_integer address,
  unsigned size)
{
  // randomize memory region
  for(unsigned i=0; i<size; i++, ++address)
  {
    if(address<memory.size()) {
      memory_cellt &cell= memory[integer2size_t(address)];
      cell.value=0;
      cell.initialised=0;
    }
  }
}

/*******************************************************************\

Function: interpretert::clear_input_flags

  Inputs:

 Outputs:

 Purpose: Clears memoy r/w flag initialization 

\*******************************************************************/

void interpretert::clear_input_flags()
{
  for(unsigned long i=0; i<memory.size(); i++) {
    const memory_cellt &cell=memory[i];
    if (cell.initialised>0) cell.initialised=0;
  }
}


/*******************************************************************\

Function: interpretert::extract_member_at

  Inputs:

 Outputs:

 Purpose:
// Side-effect: moves source_iter forwards
// appropriately to the types it walks over.

// Seems quite likely there's another recursion over datatypes that this
// could be merged with, but haven't found an ideal candidate yet.

\*******************************************************************/

bool interpretert::extract_member_at(
  std::vector<mp_integer>::iterator& source_iter,
  const std::vector<mp_integer>::iterator source_end,
  const typet& source_type,
  mp_integer offset,
  const typet& target_type,
  std::vector<mp_integer> &dest,
  bool should_return_this) const
{
  // Should allow any primitive reinterpretation here.
  bool return_this = should_return_this ||
    (offset==0 &&
     (source_type==target_type ||
      (source_type.id()==ID_pointer && target_type.id()==ID_pointer)));

  if(source_type.id()==ID_struct)
  {
    const auto& st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator offsets(st,ns);
    while(offsets->first<components.size() && offsets->second!=-1 
       && offsets->second<=offset)
    {
      if(!extract_member_at(source_iter,source_end,
                            components[offsets->first].type(),
                            offset-offsets->second,
                            target_type,dest,return_this))
        return false;
      ++offsets;
    }
    if(offsets->second==-1)
      return false;
  }
  else if(source_type.id()==ID_array)
  {
    const auto& at=to_array_type(source_type);
    std::vector<mp_integer> array_size_vec;
    evaluate(at.size(),array_size_vec);
    if(array_size_vec.size()!=1)
      return false;
    mp_integer array_size=array_size_vec[0];
    mp_integer elem_size=pointer_offset_size(at.subtype(),ns);
    if(elem_size==-1)
      return false;
    mp_integer array_idx=0;
    while(offset>=0 && array_idx < array_size)
    {
      if(!extract_member_at(source_iter,source_end,at.subtype(),
                            offset,target_type,dest,return_this))
        return false;
      offset-=elem_size;
      ++array_idx;
    }
  }
  else
  {
    if(return_this)
    {
      assert(source_iter!=source_end);
      dest.push_back(*source_iter);
    }
    ++source_iter;
  }

  return true;
  
}

/*******************************************************************\

Function: interpretert::get_cell_byte_offset

  Inputs:

 Outputs:

 Purpose: used for evaluating byte-extract op-codes

\*******************************************************************/

bool interpretert::get_cell_byte_offset(
  const typet& source_type,
  mp_integer& cell_offset,
  mp_integer& result) const
{
  if(source_type.id()==ID_struct)
  {
    const auto& st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator offsets(st,ns);
    while(offsets->first<components.size() && offsets->second!=-1)
    {
      if(!get_cell_byte_offset(components[offsets->first].type(),
                               cell_offset,result))
      {
        if(result!=-1)
          result+=offsets->second;
        return false;
      }
      ++offsets;
    }
    if(offsets->second==-1)
    {
      result=-1;
      return false;
    }
  }
  else if(source_type.id()==ID_array)
  {
    const auto& at=to_array_type(source_type);
    mp_integer elem_size=pointer_offset_size(at.subtype(),ns);
    if(elem_size==-1)
    {
      result=-1;
      return false;
    }
    if(at.size().id()!=ID_constant)
      return false;
    const auto& array_size_expr=to_constant_expr(at.size());
    mp_integer array_size;
    if(to_integer(array_size_expr,array_size))
    {
      result=-1;
      return false;
    }
    
    mp_integer array_idx;
    while(cell_offset>=0 && array_idx<array_size)
    {
      if(!get_cell_byte_offset(at.subtype(),cell_offset,result))
      {
        if(result!=-1)
          result+=(elem_size*array_idx);
        return false;
      }
      ++array_idx;
    }
  }
  else
  {
    // Primitive type.
    if(cell_offset==0)
    {
      result=0;
      return false;
    }
    else
      --cell_offset;
  }

  // Ran off the end of a struct, array, or primitive -- keep walking:
  return true;
  
}

/*******************************************************************\

Function: interpretert::evaluate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::evaluate(
  const exprt &expr,
  std::vector<mp_integer> &dest) const
{
  if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_struct)
    {
      dest.reserve(get_size(expr.type()));
      bool error=false;

      forall_operands(it, expr)
      {
        if(it->type().id()==ID_code) continue;

        unsigned sub_size=get_size(it->type());
        if(sub_size==0) continue;

        std::vector<mp_integer> tmp;
        evaluate(*it, tmp);

        if(tmp.size()==sub_size)
        {
          for(unsigned i=0; i<sub_size; i++)
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
      const irep_idt &value=to_constant_expr(expr).get_value();
      if (expr.has_operands() && expr.op0().id()==ID_address_of)
      {
        evaluate(expr.op0(),dest);
        return;
      }
      if(!to_integer(expr, i))
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
      unsigned length=strlen(str)+1;
      if (show) message->warning() << "string decoding not fully implemented "
                                   << length << messaget::eom;
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
      if(it->type().id()==ID_code) continue;

      unsigned sub_size=get_size(it->type());
      if(sub_size==0) continue;
      
      std::vector<mp_integer> tmp;
      evaluate(*it, tmp);

      if(tmp.size()==sub_size)
      {
        for(unsigned i=0; i<sub_size; i++)
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
      if (show) message->error() << "nondet not implemented" << messaget::eom;
      return;
    }
    else if(side_effect.get_statement()==ID_malloc)
    {
      if (show) message->error() << "malloc not fully implemented " 
                                 << expr.type().subtype().pretty() 
                                 << messaget::eom;
      std::stringstream buffer;
      num_dynamic_objects++;
      buffer <<"interpreter::malloc_object" << num_dynamic_objects;
      irep_idt id(buffer.str().c_str());
      mp_integer address=build_memory_map(id,expr.type().subtype());
      //TODO: check array of type
      dest.push_back(address);
      return;
    }
    if (show) message->error() << "side effect not implemented " 
                               << side_effect.get_statement()
                               << messaget::eom;
  }
  else if(expr.id()==ID_bitor)
  {
    if(expr.operands().size()<2)
      throw id2string(expr.id())+" expects at least two operands";

    mp_integer final=0;
    forall_operands(it, expr)
    {
      std::vector<mp_integer> tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1) final=bitwise_or(final,tmp.front());
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
      std::vector<mp_integer> tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1) final=bitwise_and(final,tmp.front());
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
      std::vector<mp_integer> tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1) final=bitwise_xor(final,tmp.front());
    }
    dest.push_back(final);
    return;
  }
  else if(expr.id()==ID_bitnot)
  {
    if(expr.operands().size()!=1)
      throw id2string(expr.id())+" expects one operand";
    std::vector<mp_integer> tmp;
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

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=logic_left_shift(tmp0.front(),tmp1.front(),
                                        get_size(expr.op0().type()));
      dest.push_back(final);
      return;
    }
  }
  else if((expr.id()==ID_shr) || (expr.id()==ID_lshr))
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=logic_right_shift(tmp0.front(),tmp1.front(),
                                         get_size(expr.op0().type()));
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_ashr)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      dest.push_back(tmp0.front()/power(2, tmp1.front()));
      return;
    }
  }
  else if(expr.id()==ID_ror)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=rotate_right(tmp0.front(),tmp1.front(),
                                    get_size(expr.op0().type()));
      dest.push_back(final);
      return;
    }
  }
  else if(expr.id()==ID_rol)
  {
    if(expr.operands().size()!=2)
      throw id2string(expr.id())+" expects two operands";

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    if(tmp0.size()==1 && tmp1.size()==1)
    {
      mp_integer final=rotate_left(tmp0.front(),tmp1.front(),
                                   get_size(expr.op0().type()));
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

    std::vector<mp_integer> tmp0, tmp1;
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
    if(expr.operands().size()<1)
      throw id2string(expr.id())+" expects at least one operand";
      
    bool result=false;

    forall_operands(it, expr)
    {
      std::vector<mp_integer> tmp;
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
      
    std::vector<mp_integer> tmp0, tmp1;
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
    if(expr.operands().size()<1)
      throw id2string(expr.id())+" expects at least one operand";
      
    bool result=true;

    forall_operands(it, expr)
    {
      std::vector<mp_integer> tmp;
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
      
    std::vector<mp_integer> tmp;
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
      std::vector<mp_integer> tmp;
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
      f.spec=to_fixedbv_type(expr.type());
      f.from_integer(1);
      result=f.get_value();
    }
    else if(expr.type().id()==ID_floatbv)
    {
      ieee_floatt f;
      f.spec=to_floatbv_type(expr.type());
      f.from_integer(1);
      result=f.pack();
    }
    else
      result=1;

    forall_operands(it, expr)
    {
      std::vector<mp_integer> tmp;
      evaluate(*it, tmp);
      if(tmp.size()==1)
      {
        if(expr.type().id()==ID_fixedbv)
        {
          fixedbvt f1, f2;
          f1.spec=to_fixedbv_type(expr.type());
          f2.spec=to_fixedbv_type(it->type());
          f1.set_value(result);
          f2.set_value(tmp.front());
          f1*=f2;
          result=f1.get_value();
        }
        else if(expr.type().id()==ID_floatbv)
        {
          ieee_floatt f1, f2;
          f1.spec=to_floatbv_type(expr.type());
          f2.spec=to_floatbv_type(it->type());
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

    std::vector<mp_integer> tmp0, tmp1;
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

    std::vector<mp_integer> tmp0, tmp1;
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

    std::vector<mp_integer> tmp0;
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
    std::vector<mp_integer> result;
    evaluate(expr.op0(),result);
    if(result.size()==1)
    {
      // Return the distance, in bytes, between the address returned
      // and the beginning of the underlying object.
      mp_integer address=result[0];
      if(address > 0 && address < memory.size())
      {
        const auto& memory_record=memory[integer2unsigned(address)];
        auto obj_type=get_type(memory_record.identifier);

        mp_integer offset=memory_record.offset;
        mp_integer byte_offset=-1;
        get_cell_byte_offset(obj_type,offset,byte_offset);
        if(byte_offset!=-1)
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
    std::vector<mp_integer> extract_offset;
    evaluate(expr.op1(),extract_offset);
    std::vector<mp_integer> extract_from;
    evaluate(expr.op0(),extract_from);    
    if(extract_offset.size()==1 && extract_from.size()!=0)
    {
      const typet& target_type=expr.type();
      auto extract_from_iter=extract_from.begin();

      if(extract_member_at(extract_from_iter,extract_from.end(),
                           expr.op0().type(),extract_offset[0],
                           target_type,dest,false)
         && dest.size()!=0) {
        return;
      }
    }
  }
  else if(expr.id()==ID_dereference ||
          expr.id()==ID_index ||
          expr.id()==ID_symbol ||
          expr.id()==ID_member)
  {
    mp_integer a=evaluate_address(expr, /*fail quietly=*/true);
    if(a.is_zero() && expr.id()==ID_index)
    {
      // Try reading from a constant array:
      std::vector<mp_integer> idx;
      evaluate(expr.op1(),idx);
      if(idx.size()==1)
      {
        mp_integer read_from_index=idx[0];
        if(expr.op0().id()==ID_array)
        {
          const auto& ops=expr.op0().operands();
          assert(read_from_index.is_long());
          if(read_from_index >= 0 && read_from_index < ops.size())
          {
            evaluate(ops[read_from_index.to_long()],dest);
            if(dest.size()!=0)
              return;
          }
        }
        else if(expr.op0().id()=="array-list")
        {
          // This sort of construct comes from boolbv_get, but doesn't seem
          // to have an exprt yet. Its operands are a list of key-value pairs.
          const auto& ops=expr.op0().operands();
          assert(ops.size() % 2 == 0);
          for(size_t listidx=0,listlim=ops.size();listidx!=listlim; listidx+=2)
          {
            std::vector<mp_integer> elem_idx;
            evaluate(ops[listidx],elem_idx);
            assert(elem_idx.size()==1);
            if(elem_idx[0]==read_from_index)
            {
              evaluate(ops[listidx+1],dest);
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
    else if(!a.is_zero())
    {
      dest.resize(get_size(expr.type()));
      read(a, dest);
      return;
    }
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast expects one operand";
      
    std::vector<mp_integer> tmp;
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
      else if((expr.type().id()==ID_bool)||(expr.type().id()==ID_c_bool))
      {
        dest.push_back(value!=0);
        return;
      }
    }
  }
  else if ((expr.id()==ID_array) || (expr.id()==ID_array_of))
  {
    forall_operands(it,expr) {
      evaluate(*it,dest);
    }
    return;
  }
  else if (expr.id()==ID_nil)
  {
    dest.push_back(0);
    return;
  }
  else if(expr.id()==ID_infinity)
  {
    if(expr.type().id()==ID_signedbv)
    {
      message->error() << "Infinite size arrays not supported" << messaget::eom;
      return;
    }
  }
//  if (!show) return;
  message->error() << "!! failed to evaluate expression: "
            << from_expr(ns, function->first, expr)
            << messaget::eom;
  message->error() << expr.id() << "[" << expr.type().id() << "]" 
                   << messaget::eom;
}

/*******************************************************************\

Function: interpretert::evaluate_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer interpretert::evaluate_address(const exprt &expr,
                                          bool fail_quietly) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=
      is_ssa_expr(expr) ?
      to_ssa_expr(expr).get_original_name() :
      expr.get(ID_identifier);

    interpretert::memory_mapt::const_iterator m_it1=
      memory_map.find(identifier);

    if(m_it1!=memory_map.end()) return m_it1->second;
    
    if(!call_stack.empty())
    {
      interpretert::memory_mapt::const_iterator m_it2=
        call_stack.top().local_map.find(identifier);
   
      if(m_it2!=call_stack.top().local_map.end())
        return m_it2->second;
    }
    mp_integer address=memory.size();
    build_memory_map(to_symbol_expr(expr).get_identifier(),expr.type());
    return address;

  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference expects one operand";

    std::vector<mp_integer> tmp0;
    evaluate(expr.op0(), tmp0);

    if(tmp0.size()==1)
      return tmp0.front();
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expects two operands";

    std::vector<mp_integer> tmp1;
    evaluate(expr.op1(), tmp1);

    if(tmp1.size()==1)
    {
      auto base=evaluate_address(expr.op0(),fail_quietly);
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

    const struct_typet::componentst &components=
      struct_type.components();

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->get_name()==component_name)
        break;

      offset+=get_size(it->type());
    }    

    auto base=evaluate_address(expr.op0(),fail_quietly);
    if(!base.is_zero())
      return base+offset;
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    if(expr.operands().size()!=2)
      throw "byte_extract should have two operands";    
    std::vector<mp_integer> extract_offset;
    evaluate(expr.op1(),extract_offset);
    std::vector<mp_integer> extract_from;
    evaluate(expr.op0(),extract_from);
    if(extract_offset.size()==1 && extract_from.size()!=0)
    {
      const typet& target_type=expr.type();
      auto extract_from_iter=extract_from.begin();
      std::vector<mp_integer> dest;

      /* Side-effect of extract_member_at: moves extract_from_iter to point
       * after the extracted members.*/
      if(extract_member_at(extract_from_iter,extract_from.end(),
                           expr.op0().type(),extract_offset[0],
                           target_type,dest,false)
         && dest.size()!=0) {
        mp_integer walked_over_addresses=
                   std::distance(extract_from.begin(),extract_from_iter);
        // Give address of first relevant cell.
        walked_over_addresses-=dest.size(); 
        return evaluate_address(expr.op0(),fail_quietly)+walked_over_addresses;
      }
    }    
  }
  else if(expr.id()==ID_if)
  {
    std::vector<mp_integer> result;
    if_exprt address_cond(expr.op0(),
                          address_of_exprt(expr.op1()),
                          address_of_exprt(expr.op2()));
    evaluate(address_cond,result);
    if(result.size()==1)
      return result[0];
  }
  if(!fail_quietly)
  {
    message->error() << "!! failed to evaluate address: "
              << from_expr(ns, function->first, expr)
              << messaget::eom;
  }

  return 0;
}
