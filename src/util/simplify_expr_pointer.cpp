/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "simplify_expr_class.h"
#include "expr.h"
#include "namespace.h"
#include "std_expr.h"
#include "pointer_offset_size.h"
#include "arith_tools.h"
#include "config.h"
#include "expr_util.h"

/*******************************************************************\

Function: is_dereference_integer_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_dereference_integer_object(
  const exprt &expr,
  mp_integer &address)
{
  if(expr.id()==ID_dereference &&
     expr.operands().size()==1)
  {
    if(expr.op0().id()==ID_typecast &&
       expr.op0().operands().size()==1 &&
       expr.op0().op0().is_constant() &&
       !to_integer(expr.op0().op0(), address))
      return true;

    if(expr.op0().is_constant())
    {
      if(to_constant_expr(expr.op0()).get_value()==ID_NULL &&
         config.ansi_c.NULL_is_zero) // NULL
      {
        address=0;
        return true;
      }
      else if(!to_integer(expr.op0(), address))
        return true;
    }
  }
  
  return false;
}

/*******************************************************************\

Function: simplify_exprt::simplify_address_of_arg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_address_of_arg(exprt &expr)
{
  if(expr.id()==ID_index)
  {
    if(expr.operands().size()==2)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0())) result=false;
      if(!simplify_rec(expr.op1())) result=false;

      // rewrite (*(type *)int) [index] by
      // pushing the index inside
      
      mp_integer address;
      if(is_dereference_integer_object(expr.op0(), address))
      {
        // push index into address
        
        mp_integer step_size, index;
        
        step_size=pointer_offset_size(expr.type(), ns);
        
        if(!to_integer(expr.op1(), index) &&
           step_size!=-1)
        {
          unsignedbv_typet int_type(config.ansi_c.pointer_width);
          pointer_typet pointer_type;
          pointer_type.subtype()=expr.type();
          typecast_exprt typecast_expr(
            from_integer(step_size*index+address, int_type), pointer_type);
          exprt new_expr=dereference_exprt(typecast_expr, expr.type());
          expr=new_expr;
          result=true;
        }
      }

      return result;
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()==1)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0())) result=false;

      const typet &op_type=ns.follow(expr.op0().type());

      if(op_type.id()==ID_struct)
      {
        // rewrite NULL -> member by
        // pushing the member inside

        mp_integer address;
        if(is_dereference_integer_object(expr.op0(), address))
        {
          const struct_typet &struct_type=to_struct_type(op_type);
          const irep_idt &member=to_member_expr(expr).get_component_name();
          mp_integer offset=member_offset(struct_type, member, ns);
          if(offset!=-1)
          {
            unsignedbv_typet int_type(config.ansi_c.pointer_width);
            pointer_typet pointer_type;
            pointer_type.subtype()=expr.type();
            typecast_exprt typecast_expr(
              from_integer(address+offset, int_type), pointer_type);
            exprt new_expr=dereference_exprt(typecast_expr, expr.type());
            expr=new_expr;
            result=true;
          }          
        }
      }
      
      return result;
    }
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()==1)
      return simplify_rec(expr.op0());
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()==3)
    {
      bool result=true;
      if(!simplify_rec(expr.op0())) result=false;
      if(!simplify_address_of_arg(expr.op1())) result=false;
      if(!simplify_address_of_arg(expr.op2())) result=false;

      // op0 is a constant?
      if(expr.op0().is_true())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op1());
        expr.swap(tmp);
      }
      else if(expr.op0().is_false())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op2());
        expr.swap(tmp);
      }
      
      return result;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_address_of(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  if(ns.follow(expr.type()).id()!=ID_pointer) return true;
  
  exprt &object=expr.op0();
  
  bool result=simplify_address_of_arg(object);
  
  if(object.id()==ID_index)
  {
    index_exprt &index_expr=to_index_expr(object);
  
    if(!index_expr.index().is_zero())
    {
      // we normalize &a[i] to (&a[0])+i
      exprt offset;
      offset.swap(index_expr.op1());
      index_expr.op1()=gen_zero(offset.type());

      exprt addition(ID_plus, expr.type());
      addition.move_to_operands(expr, offset);
      
      expr.swap(addition);
      return false;
    }
  }
  else if(object.id()==ID_dereference)
  {
    // simplify &*p to p
    assert(object.operands().size()==1);
    exprt tmp=object.op0();
    expr=tmp;
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_pointer_offset(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  exprt &ptr=expr.op0();

  if(ptr.id()==ID_if && ptr.operands().size()==3)
  {
    const if_exprt &if_expr=to_if_expr(ptr);

    exprt tmp_op1=expr;
    tmp_op1.op0()=if_expr.true_case();
    simplify_pointer_offset(tmp_op1);
    exprt tmp_op2=expr;
    tmp_op2.op0()=if_expr.false_case();
    simplify_pointer_offset(tmp_op2);

    expr=if_exprt(if_expr.cond(), tmp_op1, tmp_op2);

    simplify_if(expr);

    return false;
  }

  if(ptr.type().id()!=ID_pointer) return true;
  
  if(ptr.id()==ID_address_of)
  {
    if(ptr.operands().size()!=1) return true;

    mp_integer offset=compute_pointer_offset(ptr.op0(), ns);

    if(offset!=-1)
    {
      expr=from_integer(offset, expr.type());
      return false;
    }    
  }
  else if(ptr.id()==ID_typecast) // pointer typecast
  {
    if(ptr.operands().size()!=1) return true;
    
    const typet &op_type=ns.follow(ptr.op0().type());
    
    if(op_type.id()==ID_pointer)
    {
      // Cast from pointer to pointer.
      // This just passes through, remove typecast.
      exprt tmp=ptr.op0();
      ptr=tmp;
    
      // recursive call
      simplify_node(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
    {
      // Cast from integer to pointer, say (int *)x.
      
      if(ptr.op0().is_constant())
      {
        // (T *)0x1234 -> 0x1234
        exprt tmp=ptr.op0();
        tmp.make_typecast(expr.type());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else
      {
        // We do a bit of special treatment for (TYPE *)(a+(int)&o),
        // which is re-written to 'a'.

        typet type=ns.follow(expr.type());      
        exprt tmp=ptr.op0();
        if(tmp.id()==ID_plus && tmp.operands().size()==2)
        {
          if(tmp.op0().id()==ID_typecast &&
             tmp.op0().operands().size()==1 &&
             tmp.op0().op0().id()==ID_address_of)
          {
            expr=tmp.op1();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
          }
          else if(tmp.op1().id()==ID_typecast &&
                  tmp.op1().operands().size()==1 &&
                  tmp.op1().op0().id()==ID_address_of)
          {
            expr=tmp.op0();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
          }
        }
      }
    }
  }
  else if(ptr.id()==ID_plus) // pointer arithmetic
  {
    exprt::operandst ptr_expr;
    exprt::operandst int_expr;
    
    forall_operands(it, ptr)
    {
      if(it->type().id()==ID_pointer)
        ptr_expr.push_back(*it);
      else if(!it->is_zero())
      {
        exprt tmp=*it;
        if(tmp.type()!=expr.type())
        {
          tmp.make_typecast(expr.type());
          simplify_node(tmp);
        }
        
        int_expr.push_back(tmp);
      }
    }

    if(ptr_expr.size()!=1 || int_expr.empty())
      return true;
      
    typet pointer_type=ptr_expr.front().type();

    mp_integer element_size=
      pointer_offset_size(pointer_type.subtype(), ns);
    
    if(element_size==0) return true;
    
    // this might change the type of the pointer!
    exprt ptr_off(ID_pointer_offset, expr.type());
    ptr_off.copy_to_operands(ptr_expr.front());
    simplify_node(ptr_off);

    exprt sum;
    
    if(int_expr.size()==1)
      sum=int_expr.front();
    else
    {
      sum=exprt(ID_plus, expr.type());
      sum.operands()=int_expr;
    }
      
    simplify_node(sum);
    
    exprt size_expr=
      from_integer(element_size, expr.type());
        
    binary_exprt product(sum, ID_mult, size_expr, expr.type());
  
    simplify_node(product);
    
    expr=binary_exprt(ptr_off, ID_plus, product, expr.type());

    simplify_node(expr);
    
    return false;
  }
  else if(ptr.id()==ID_constant &&
          ptr.get(ID_value)==ID_NULL)
  {
    expr=gen_zero(expr.type());

    simplify_node(expr);

    return false;
  }

  return true;
}

