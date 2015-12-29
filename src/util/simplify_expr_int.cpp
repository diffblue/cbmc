/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "simplify_expr_class.h"
#include "expr.h"
#include "namespace.h"
#include "std_expr.h"
#include "expr_util.h"
#include "arith_tools.h"
#include "fixedbv.h"
#include "rational_tools.h"
#include "simplify_utils.h"
#include "ieee_float.h"

/*******************************************************************\

Function: simplify_exprt::simplify_mult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_mult(exprt &expr)
{
  // check to see if it is a number type
  if(!is_number(expr.type()))
    return true;

  // vector of operands
  exprt::operandst &operands=expr.operands();

  // result of the simplification
  bool result = true;

  // position of the constant
  exprt::operandst::iterator constant;

  // true if we have found a constant
  bool found = false;
  
  typet c_sizeof_type=nil_typet();

  // scan all the operands
  for(exprt::operandst::iterator it=operands.begin();
      it!=operands.end();)
  {
    // if one of the operands is not a number return
    if(!is_number(it->type())) return true;

    // if one of the operands is zero the result is zero
    // note: not true on IEEE floating point arithmetic
    if(it->is_zero() &&
       it->type().id()!=ID_floatbv)
    {
      expr=gen_zero(expr.type());
      return false;
    }

    // true if the given operand has to be erased
    bool do_erase = false;

    // if this is a constant of the same time as the result
    if(it->is_constant() && it->type()==expr.type())
    {
      // preserve the sizeof type annotation
      if(c_sizeof_type.is_nil())
        c_sizeof_type=
          static_cast<const typet &>(it->find(ID_C_c_sizeof_type));

      if(found)
      {
        // update the constant factor
        if(!constant->mul(*it)) do_erase=true;
      }
      else
      {
        // set it as the constant factor if this is the first
        constant=it;
        found=true;
      }
    }

    // erase the factor if necessary
    if(do_erase)
    {
      it=operands.erase(it);
      result = false;
    }
    else
      it++; // move to the next operand
  }
  
  if(c_sizeof_type.is_not_nil())
  {
    assert(found);
    constant->set(ID_C_c_sizeof_type, c_sizeof_type);
  }

  if(operands.size()==1)
  {
    exprt product(operands.front());
    expr.swap(product);

    result = false;
  }
  else
  {
    // if the constant is a one and there are other factors
    if(found && constant->is_one())
    {
      // just delete it
      operands.erase(constant);
      result=false;

      if(operands.size()==1)
      {
        exprt product(operands.front());
        expr.swap(product);
      }
    }
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_div(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;
    
  const typet &expr_type=expr.type();

  if(expr_type!=expr.op0().type() ||
     expr_type!=expr.op1().type())
    return true;

  if(expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_natural ||
     expr_type.id()==ID_integer)
  {
    mp_integer int_value0, int_value1;
    bool ok0, ok1;

    ok0=!to_integer(expr.op0(), int_value0);
    ok1=!to_integer(expr.op1(), int_value1);

    // division by zero?
    if(ok1 && int_value1==0)
      return true;

    // x/1?
    if(ok1 && int_value1==1)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    // 0/x?
    if(ok0 && int_value0==0)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      mp_integer result=int_value0/int_value1;
      exprt tmp=from_integer(result, expr_type);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_rational)
  {
    rationalt rat_value0, rat_value1;
    bool ok0, ok1;

    ok0=!to_rational(expr.op0(), rat_value0);
    ok1=!to_rational(expr.op1(), rat_value1);

    if(ok1 && rat_value1.is_zero())
      return true;

    if((ok1 && rat_value1.is_one()) ||
       (ok0 && rat_value0.is_zero()))
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(ok0 && ok1)
    {
      rationalt result=rat_value0/rat_value1;
      exprt tmp=from_rational(result);

      if(tmp.is_not_nil())
      {
        expr.swap(tmp);
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    // division by one?
    if(expr.op1().is_constant() &&
       expr.op1().is_one())
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }

    if(expr.op0().is_constant() &&
       expr.op1().is_constant())
    {
      fixedbvt f0(to_constant_expr(expr.op0()));
      fixedbvt f1(to_constant_expr(expr.op1()));
      if(!f1.is_zero())
      {
        f0/=f1;
        expr=f0.to_expr();
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_mod(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  if(expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_natural ||
     expr.type().id()==ID_integer)
  {
    if(expr.type()==expr.op0().type() &&
       expr.type()==expr.op1().type())
    {
      mp_integer int_value0, int_value1;
      bool ok0, ok1;

      ok0=!to_integer(expr.op0(), int_value0);
      ok1=!to_integer(expr.op1(), int_value1);

      if(ok1 && int_value1==0)
        return true; // division by zero

      if((ok1 && int_value1==1) ||
         (ok0 && int_value0==0))
      {
        expr=gen_zero(expr.type());
        return false;
      }

      if(ok0 && ok1)
      {
        mp_integer result=int_value0%int_value1;
        exprt tmp=from_integer(result, expr.type());

        if(tmp.is_not_nil())
        {
          expr.swap(tmp);
          return false;
        }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_plus(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  bool result=true;

  exprt::operandst &operands=expr.operands();
  
  assert(expr.id()==ID_plus);

  // floating-point addition is _NOT_ associative; thus,
  // there is special case for float
  
  if(ns.follow(expr.type()).id()==ID_floatbv)
  {
    // we only merge neighboring constants!
    Forall_expr(it, operands)
    {
      exprt::operandst::iterator next=it;
      next++;
      
      if(next!=operands.end())
      {
        if(it->type()==next->type() &&
           it->is_constant() &&
           next->is_constant())
        {
          it->sum(*next);
          operands.erase(next);
        }
      }
    }
  }
  else
  {
    // ((T*)p+a)+b -> (T*)p+(a+b)
    if(expr.type().id()==ID_pointer &&
       expr.operands().size()==2 &&
       expr.op0().id()==ID_plus &&
       expr.op0().operands().size()==2)
    {
      exprt op0=expr.op0();

      if(expr.op0().op1().id()==ID_plus)
        op0.op1().copy_to_operands(expr.op1());
      else
        op0.op1()=plus_exprt(op0.op1(), expr.op1());

      expr.swap(op0);

      simplify_plus(expr.op1());
      simplify_plus(expr);

      return false;
    }

    // count the constants
    size_t count=0;
    forall_operands(it, expr)
      if(is_number(it->type()) && it->is_constant())
        count++;
    
    // merge constants?
    if(count>=2)
    {
      exprt::operandst::iterator const_sum;
      bool const_sum_set=false;

      Forall_operands(it, expr)
      {
        if(is_number(it->type()) && it->is_constant())
        {
          if(!const_sum_set)
          {
            const_sum=it;
            const_sum_set=true;
          }
          else
          {
            if(!const_sum->sum(*it))
            {
              *it=gen_zero(it->type());
              result=false;
            }
          }
        }
      }
    }
    
    // search for a and -a
    // first gather all the a's with -a
    typedef hash_map_cont<exprt, exprt::operandst::iterator, irep_hash>
      expr_mapt;
    expr_mapt expr_map;

    Forall_expr(it, operands)
      if(it->id()==ID_unary_minus &&
         it->operands().size()==1)
        expr_map.insert(std::make_pair(it->op0(), it));

    // now search for a
    Forall_expr(it, operands)
    {
      if(expr_map.empty()) break;
      else if(it->id()==ID_unary_minus) continue;

      expr_mapt::iterator itm=expr_map.find(*it);

      if(itm!=expr_map.end())
      {
        *(itm->second)=gen_zero(expr.type());
        *it=gen_zero(expr.type());
        expr_map.erase(itm);
        result=false;
      }
    }

    // delete zeros
    // (can't do for floats, as the result of 0.0 + (-0.0)
    // need not be -0.0 in std rounding)
    for(exprt::operandst::iterator
        it=operands.begin();
        it!=operands.end();
        /* no it++ */)
    {
      if(is_number(it->type()) && it->is_zero())
      {
        it=operands.erase(it);
        result=false;
      }
      else
        it++;
    }
  }

  if(operands.empty())
  {
    expr=gen_zero(expr.type());
    return false;
  }
  else if(operands.size()==1)
  {
    exprt tmp(operands.front());
    expr.swap(tmp);
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_minus(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  exprt::operandst &operands=expr.operands();

  assert(expr.id()==ID_minus);

  if(operands.size()!=2)
    return true;
  
  if(is_number(expr.type()) &&
     is_number(operands[0].type()) &&
     is_number(operands[1].type()))
  {
    // rewrite "a-b" to "a+(-b)"
    unary_minus_exprt tmp2(operands[1]);
    simplify_unary_minus(tmp2);

    plus_exprt tmp(operands[0], tmp2);
    simplify_plus(tmp);

    expr.swap(tmp);
    return false;
  }
  else if(expr.type().id()==ID_pointer &&
          operands[0].type().id()==ID_pointer &&
          is_number(operands[1].type()))
  {
    // pointer arithmetic: rewrite "p-i" to "p+(-i)"
    unary_minus_exprt tmp2(operands[1]);
    simplify_unary_minus(tmp2);

    plus_exprt tmp(operands[0], tmp2);
    simplify_plus(tmp);

    expr.swap(tmp);
    return false;
  }
  else if(is_number(expr.type()) &&
          operands[0].type().id()==ID_pointer &&
          operands[1].type().id()==ID_pointer)
  {
    // pointer arithmetic: rewrite "p-p" to "0"
    
    if(operands[0]==operands[1])
    {
      exprt zero=gen_zero(expr.type());
      if(zero.is_not_nil())
      {
        expr=zero;
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_bitwise

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_bitwise(exprt &expr)
{
  if(!is_bitvector_type(expr.type()))
    return true;
    
  // check if these are really boolean
  if(expr.type().id()!=ID_bool)
  {
    bool all_bool=true;
    
    forall_operands(it, expr)
    {
      if(it->id()==ID_typecast &&
         it->operands().size()==1 &&
         ns.follow(it->op0().type()).id()==ID_bool)
      {
      }
      else if(it->is_zero() || it->is_one())
      {
      }
      else
        all_bool=false;
    }
        
    if(all_bool)
    {
      // re-write to boolean+typecast
      exprt new_expr=expr;
      
      if(expr.id()==ID_bitand)
        new_expr.id(ID_and);
      else if(expr.id()==ID_bitor)
        new_expr.id(ID_or);
      else if(expr.id()==ID_bitxor)
        new_expr.id(ID_xor);
      else
        assert(false);
        
      Forall_operands(it, new_expr)
      {
        if(it->id()==ID_typecast)
        {
          exprt tmp;
          tmp=it->op0();
          it->swap(tmp);
        }
        else if(it->is_zero())
          *it=false_exprt();
        else if(it->is_one())
          *it=true_exprt();
      }
        
      new_expr.type()=bool_typet();
      simplify_node(new_expr);

      new_expr.make_typecast(expr.type());
      simplify_node(new_expr);
      
      expr.swap(new_expr);
      return false;
    }
  }

  bool result=true;
    
  // try to merge constants
  
  unsigned width=to_bitvector_type(expr.type()).get_width();
    
  while(expr.operands().size()>=2)
  {
    const irep_idt &a_str=expr.op0().get(ID_value);
    const irep_idt &b_str=expr.op1().get(ID_value);
    
    if(!expr.op0().is_constant())
      break;
      
    if(!expr.op1().is_constant())
      break;
      
    if(expr.op0().type()!=expr.type())
      break;
                
    if(expr.op1().type()!=expr.type())
      break;
      
    assert(a_str.size()==b_str.size());
      
    constant_exprt new_op(expr.type());
    std::string new_value;
    new_value.resize(width);
                
    if(expr.id()==ID_bitand)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=(a_str[i]=='1' && b_str[i]=='1')?'1':'0';
    }
    else if(expr.id()==ID_bitor)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=(a_str[i]=='1' || b_str[i]=='1')?'1':'0';
    }
    else if(expr.id()==ID_bitxor)
    {
      for(unsigned i=0; i<width; i++)
        new_value[i]=((a_str[i]=='1')!=(b_str[i]=='1'))?'1':'0';
    }
    else
      break;
      
    new_op.set_value(new_value);

    // erase first operand
    expr.operands().erase(expr.operands().begin());
    expr.op0().swap(new_op);
    
    result=false;
  }

  // now erase zeros out of bitor, bitxor

  if(expr.id()==ID_bitor || expr.id()==ID_bitxor)
  {
    for(exprt::operandst::iterator
        it=expr.operands().begin();
        it!=expr.operands().end();
        ) // no it++
    {
      if(it->is_zero() && expr.operands().size()>1)
      {
        it=expr.operands().erase(it);
        result=false;
      }
      else
        it++;
    }
  }
  
  // two operands that are syntactically the same

  if(expr.operands().size()==2 &&
     expr.op0()==expr.op1())
  {
    if(expr.id()==ID_bitand || expr.id()==ID_bitor)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      return false;
    }
    else if(expr.id()==ID_bitxor)
    {
      constant_exprt new_op(expr.type());
      new_op.set_value(integer2binary(0, width));
      expr.swap(new_op);
      return false;
    }
  }
  
  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_extractbit(exprt &expr)
{
  const typet &op0_type=expr.op0().type();

  if(!is_bitvector_type(op0_type))
    return true;
  
  unsigned width=to_bitvector_type(op0_type).get_width();

  assert(expr.operands().size()==2);

  mp_integer i;

  if(to_integer(expr.op1(), i))
    return true;

  if(!expr.op0().is_constant())
    return true;

  if(i<0 || i>=width)
    return true;

  const irep_idt &value=expr.op0().get(ID_value);

  if(value.size()!=width)
    return true;

  bool bit=(id2string(value)[width-integer2long(i)-1]=='1');

  expr.make_bool(bit);

  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_concatenation(exprt &expr)
{
  bool result=true;

  if(is_bitvector_type(expr.type()))
  {
    // first, turn bool into bvec[1]
    Forall_operands(it, expr)
    {
      exprt &op=*it;
      if(op.is_true() || op.is_false())
      {
        bool value=op.is_true();
        op=constant_exprt(value?ID_1:ID_0, unsignedbv_typet(1));
      }
    }
    
    // search for neighboring constants to merge
    size_t i=0;
    
    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];
    
      if(opi.is_constant() &&
         opn.is_constant() &&
         is_bitvector_type(opi.type()) &&
         is_bitvector_type(opn.type()))
      {
        // merge!
        const std::string new_value=
          opi.get_string(ID_value)+opn.get_string(ID_value);
        opi.set(ID_value, new_value);
        opi.type().set(ID_width, new_value.size());
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result=true;
      }
      else
        i++;
    }
  }
  else if(expr.type().id()==ID_verilog_unsignedbv)
  {
    // search for neighboring constants to merge
    size_t i=0;
    
    while(i<expr.operands().size()-1)
    {
      exprt &opi=expr.operands()[i];
      exprt &opn=expr.operands()[i+1];
    
      if(opi.is_constant() &&
         opn.is_constant() &&
         (opi.type().id()==ID_verilog_unsignedbv || is_bitvector_type(opi.type())) &&
         (opn.type().id()==ID_verilog_unsignedbv || is_bitvector_type(opn.type())))
      {
        // merge!
        const std::string new_value=
          opi.get_string(ID_value)+opn.get_string(ID_value);
        opi.set(ID_value, new_value);
        opi.type().set(ID_width, new_value.size());
        opi.type().id(ID_verilog_unsignedbv);
        // erase opn
        expr.operands().erase(expr.operands().begin()+i+1);
        result=true;
      }
      else
        i++;
    }
  }

  // { x } = x
  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    result=false;
  }
  
  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_shifts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_shifts(exprt &expr)
{
  if(!is_number(expr.type()))
    return true;

  if(expr.operands().size()!=2)
    return true;

  mp_integer distance;
  
  if(to_integer(expr.op1(), distance))
    return true;
    
  if(distance==0)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  mp_integer value;
  
  if(to_integer(expr.op0(), value))
    return true;

  if(expr.op0().type().id()==ID_unsignedbv || 
     expr.op0().type().id()==ID_signedbv)
  { 
    mp_integer width=
      string2integer(id2string(expr.op0().type().get(ID_width)));
      
    if(expr.id()==ID_lshr)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=gen_zero(expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      if(distance>=0)
      {
        // this is to simulate an arithmetic right shift
        mp_integer new_value=value >> distance;
        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      // this is to guard against large values of distance
      if(distance>=width)
      {
        expr=gen_zero(expr.type());
        return false;
      }
      else if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_integer ||
          expr.op0().type().id()==ID_natural)
  {
    if(expr.id()==ID_lshr)
    {
      if(distance>=0)
      {
        value/=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_ashr)
    {
      // this is to simulate an arithmetic right shift
      if(distance>=0)
      {
        mp_integer new_value=value/power(2, distance);
        if(value<0 && new_value==0) new_value=-1;

        expr=from_integer(new_value, expr.type());
        return false;
      }
    }
    else if(expr.id()==ID_shl)
    {
      if(distance>=0)
      {
        value*=power(2, distance);
        expr=from_integer(value, expr.type());
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: sort_and_join

  Inputs:

 Outputs:

 Purpose: produce canonical ordering for associative and commutative
          binary operators

\*******************************************************************/

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
  { ID_bitand,{ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitor, {ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { ID_bitxor,{ID_unsignedbv ,
               ID_signedbv   ,
               ID_floatbv    ,
               ID_fixedbv    ,
               irep_idt()  }},
  { irep_idt(),{ irep_idt() }}
};

static bool sort_and_join(
  const struct saj_tablet &saj_entry,
  const irep_idt &type_id)
{
  for(unsigned i=0; saj_entry.type_ids[i]!=irep_idt(); i++)
    if(type_id==saj_entry.type_ids[i])
      return true;

  return false;
}

static const struct saj_tablet &sort_and_join(
  const irep_idt &id,
  const irep_idt &type_id)
{
  unsigned i=0;

  for( ; saj_table[i].id!=irep_idt(); i++)
    if(id==saj_table[i].id &&
       sort_and_join(saj_table[i], type_id))
      return saj_table[i];

  return saj_table[i];
}

/*******************************************************************\

Function: sort_and_join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::sort_and_join(exprt &expr)
{
  bool result=true;

  if(!expr.has_operands()) return true;

  const struct saj_tablet &saj_entry=
    ::sort_and_join(expr.id(), expr.type().id());
  if(saj_entry.id==irep_idt())
    return true;

  // check operand types

  forall_operands(it, expr)
    if(!::sort_and_join(saj_entry, it->type().id()))
      return true;

  // join expressions

  exprt::operandst new_ops;
  new_ops.reserve(expr.operands().size());

  forall_operands(it, expr)
  {
    if(it->id()==expr.id())
    {
      new_ops.reserve(new_ops.capacity()+it->operands().size()-1);

      forall_operands(it2, *it)
        new_ops.push_back(*it2);

      result=false;
    }
    else
      new_ops.push_back(*it);
  }

  // sort it

  result=sort_operands(new_ops) && result;
  expr.operands().swap(new_ops);

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_extractbits

  Inputs:

 Outputs:

 Purpose: Simplifies extracting of bits from a constant. 

\*******************************************************************/

bool simplify_exprt::simplify_extractbits(exprt &expr)
{
  assert(expr.operands().size()==3);

  const typet &op0_type=expr.op0().type();

  if(!is_bitvector_type(op0_type) &&
     !is_bitvector_type(expr.type()))
    return true;

  if(expr.op0().is_constant())
  {
    unsigned width=to_bitvector_type(op0_type).get_width();
    mp_integer start, end;
    
    if(to_integer(expr.op1(), start))
      return true;

    if(to_integer(expr.op2(), end))
      return true;

    if(start<0 || start>=width ||
       end  <0 || end  >=width)
      return true;

    assert(start>=end); //is this always the case??

    const irep_idt &value=expr.op0().get(ID_value);

    if(value.size()!=width)
      return true;

    std::string svalue=id2string(value);

    std::string extracted_value=
      svalue.substr(width-integer2long(start)-1,
                    integer2long(start-end+1));
    
    exprt tmp(ID_constant, expr.type());
    tmp.set(ID_value, extracted_value);
    expr.swap(tmp);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_unary_plus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_unary_plus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  // simply remove, this is always 'nop'
  expr=expr.op0();
  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_unary_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_unary_minus(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(!is_number(expr.type()))
    return true;

  exprt &operand=expr.op0();

  if(expr.type()!=operand.type())
    return true;

  if(operand.id()==ID_unary_minus)
  {
    // cancel out "-(-x)" to "x"
    if(operand.operands().size()!=1)
      return true;

    if(!is_number(operand.op0().type()))
      return true;

    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.swap(tmp);
    return false;
  }
  else if(operand.id()==ID_constant)
  {
    const irep_idt &type_id=expr.type().id();

    if(type_id==ID_integer ||
       type_id==ID_signedbv ||
       type_id==ID_unsignedbv)
    {
      mp_integer int_value;

      if(to_integer(expr.op0(), int_value))
        return true;

      exprt tmp=from_integer(-int_value, expr.type());

      if(tmp.is_nil())
        return true;

      expr.swap(tmp);

      return false;
    }
    else if(type_id==ID_rational)
    {
      rationalt r;
      if(to_rational(expr.op0(), r))
        return true;

      expr=from_rational(-r);
      return false;
    }
    else if(type_id==ID_fixedbv)
    {
      fixedbvt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
    else if(type_id==ID_floatbv)
    {
      ieee_floatt f(to_constant_expr(expr.op0()));
      f.negate();
      expr=f.to_expr();
      return false;
    }
  }

  return true;
}

