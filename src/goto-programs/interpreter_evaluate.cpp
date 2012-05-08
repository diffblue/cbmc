/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <ieee_float.h>
#include <fixedbv.h>
#include <std_expr.h>

#include "interpreter_class.h"

/*******************************************************************\

Function: interpretert::evaluate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpretert::read(
  mp_integer address,
  std::vector<mp_integer> &dest) const
{
  // copy memory region
  for(unsigned i=0; i<dest.size(); i++, ++address)
  {
    mp_integer value;
    
    if(address<memory.size())
      value=memory[integer2long(address)].value;
    else
      value=0;
      
    dest[i]=value;
  }
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
    else if(expr.type().id()==ID_bool)
    {
      dest.push_back(expr.is_true());
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
      
    std::vector<mp_integer> tmp0, tmp1, tmp2;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);
    evaluate(expr.op2(), tmp2);

    if(tmp0.size()==1 && tmp1.size()==1 && tmp2.size()==1)
    {
      const mp_integer &op0=tmp0.front();
      const mp_integer &op1=tmp1.front();
      const mp_integer &op2=tmp2.front();

      dest.push_back(op0!=0?op1:op2);    
    }

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
  else if(expr.id()==ID_dereference ||
          expr.id()==ID_index ||
          expr.id()==ID_symbol ||
          expr.id()==ID_member)
  {
    mp_integer a=evaluate_address(expr);
    dest.resize(get_size(expr.type()));
    read(a, dest);
    return;
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
      else if(expr.type().id()==ID_bool)
      {
        dest.push_back(value!=0);
        return;
      }
    }
  }
  else if(expr.id()==ID_ashr)
  {
    if(expr.operands().size()!=2)
      throw "ashr expects two operands";

    std::vector<mp_integer> tmp0, tmp1;
    evaluate(expr.op0(), tmp0);
    evaluate(expr.op1(), tmp1);

    if(tmp0.size()==1 && tmp1.size()==1)
      dest.push_back(tmp0.front()/power(2, tmp1.front()));

    return;
  }

  std::cout << "!! failed to evaluate expression: "
            << from_expr(ns, function->first, expr)
            << std::endl;
}

/*******************************************************************\

Function: interpretert::evaluate_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer interpretert::evaluate_address(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    
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
      return evaluate_address(expr.op0())+tmp1.front();
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

    return evaluate_address(expr.op0())+offset;
  }
  
  std::cout << "!! failed to evaluate address: "
            << from_expr(ns, function->first, expr)
            << std::endl;

  return 0;
}
