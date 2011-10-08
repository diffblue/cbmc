/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <algorithm>

#include "simplify_expr_class.h"
#include "simplify_expr.h"
#include "mp_arith.h"
#include "arith_tools.h"
#include "replace_expr.h"
#include "std_types.h"
#include "bitvector.h"
#include "simplify_utils.h"
#include "expr_util.h"
#include "std_expr.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "pointer_offset_size.h"
#include "rational.h"
#include "rational_tools.h"
#include "config.h"
#include "base_type.h"

//#define DEBUGX

#ifdef DEBUGX
#include <langapi/language_util.h>
#endif

//#define USE_CACHE

#ifdef USE_CACHE
struct simplify_expr_cachet
{
public:
  friend class simplify_exprt;

  #if 1
  typedef hash_map_cont<
    exprt, exprt, irep_full_hash, irep_full_eq> containert;
  #else
  typedef hash_map_cont<
    exprt, exprt, irep_hash> containert;
  #endif
    
  containert container_normal;
  
  containert &container()
  {
    return container_normal;
  }
};

simplify_expr_cachet simplify_expr_cache;
#endif

/*******************************************************************\

Function: simplify_exprt::simplify_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_typecast(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(expr.op0().type());
  
  // eliminate casts of infinity
  if(expr.op0().id()==ID_infinity)
  {
    typet new_type=expr.type();
    exprt tmp;
    tmp.swap(expr.op0());
    tmp.type()=new_type;
    expr.swap(tmp);
    return false;
  }
  
  // eliminate redundant typecasts
  if(base_type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  // elminiate casts to bool
  if(expr_type==bool_typet())
  {
    equal_exprt equality;
    equality.location()=expr.location();
    equality.lhs()=expr.op0();
    equality.rhs()=gen_zero(ns.follow(expr.op0().type()));
    assert(equality.rhs().is_not_nil());
    simplify_node(equality);
    equality.make_not();
    simplify_node(equality);
    expr.swap(equality);
    return false;
  }
  
  // eliminate typecasts from NULL
  if(expr_type.id()==ID_pointer &&
     expr.op0().is_constant() &&
     expr.op0().get(ID_value)==ID_NULL)
  {
    exprt tmp=expr.op0();
    tmp.type()=expr.type();
    expr.swap(tmp);
    return false;
  }

  // eliminate duplicate pointer typecasts
  if(expr_type.id()==ID_pointer &&
     expr.op0().id()==ID_typecast &&
     op_type.id()==ID_pointer &&
     expr.op0().operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.op0().swap(tmp);
    // recursive call
    simplify_node(expr);
    return false;
  }
  
  // casts from integer to pointer and back:
  // (int)(void *)int -> (int)(size_t)int
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     op_type.id()==ID_pointer)
  {
    expr.op0().type()=unsignedbv_typet(config.ansi_c.pointer_width);
    simplify_typecast(expr.op0()); // rec. call
    simplify_typecast(expr); // rec. call
    return false;
  }
  
  const irep_idt &expr_type_id=expr_type.id();
  const exprt &operand=expr.op0();
  const irep_idt &op_type_id=op_type.id();

  unsigned expr_width=bv_width(expr_type);
  unsigned op_width=bv_width(operand.type());

  if(operand.is_constant())
  {
    const irep_idt &value=operand.get(ID_value);

    exprt new_expr(ID_constant, expr.type());

    // preserve the sizeof type annotation
    typet c_sizeof_type=
      static_cast<const typet &>(operand.find(ID_C_c_sizeof_type));
      
    if(op_type_id==ID_integer ||
       op_type_id==ID_natural ||
       op_type_id==ID_c_enum ||
       op_type_id==ID_incomplete_c_enum)
    {
      // from integer to ...
    
      mp_integer int_value=string2integer(id2string(value));

      if(expr_type_id==ID_bool)
      {
        new_expr.set(ID_value, (int_value!=0)?ID_true:ID_false);
        expr.swap(new_expr);
        return false;
      }

      if(expr_type_id==ID_unsignedbv || expr_type_id==ID_signedbv)
      {
        new_expr.set(ID_value, integer2binary(int_value, expr_width));
        expr.swap(new_expr);
        return false;
      }

      if(expr_type_id==ID_integer)
      {
        new_expr.set(ID_value, value);
        expr.swap(new_expr);
        return false;
      }
      
      if(expr_type_id==ID_c_enum ||
         expr_type_id==ID_incomplete_c_enum)
      {
        new_expr.set(ID_value, integer2string(int_value));
        expr.swap(new_expr);
        return false;
      }
    }
    else if(op_type_id==ID_rational)
    {
    }
    else if(op_type_id==ID_real)
    {
    }
    else if(op_type_id==ID_bool)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_integer ||
         expr_type_id==ID_natural ||
         expr_type_id==ID_rational)
      {
        if(operand.is_true())
        {
          expr=gen_one(expr_type);
          assert(expr.is_not_nil());
          return false;
        }
        else if(operand.is_false())
        {
          expr=gen_zero(expr_type);
          assert(expr.is_not_nil());
          return false;
        }
      }
    }
    else if(op_type_id==ID_unsignedbv ||
            op_type_id==ID_signedbv)
    {
      mp_integer int_value=binary2integer(
        id2string(value), op_type_id==ID_signedbv);

      if(expr_type_id==ID_bool)
      {
        new_expr.make_bool(int_value!=0);
        expr.swap(new_expr);
        return false;
      }

      if(expr_type_id==ID_integer)
      {
        new_expr=from_integer(int_value, expr_type);
        expr.swap(new_expr);
        return false;
      }

      if(expr_type_id==ID_natural)
      {
        if(int_value>=0)
        {
          new_expr=from_integer(int_value, expr_type);
          expr.swap(new_expr);
          return false;
        }
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_bv)
      {
        new_expr.set(ID_value, integer2binary(int_value, expr_width));
        expr.swap(new_expr);

        if(c_sizeof_type.is_not_nil())
          expr.set(ID_C_c_sizeof_type, c_sizeof_type);

        return false;
      }
      
      if(expr_type_id==ID_c_enum ||
         expr_type_id==ID_incomplete_c_enum)
      {
        new_expr.set(ID_value, integer2string(int_value));
        expr.swap(new_expr);
        return false;
      }
      
      if(expr_type_id==ID_fixedbv)
      {
        // int to float
        const fixedbv_typet &f_expr_type=
          to_fixedbv_type(expr_type);

        fixedbvt f;
        f.spec=f_expr_type;
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_floatbv)
      {
        // int to float
        const floatbv_typet &f_expr_type=
          to_floatbv_type(expr_type);

        ieee_floatt f;
        f.spec=f_expr_type;
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_rational)
      {
        rationalt r=int_value;
        expr=from_rational(r);
        return false;
      }

    }
    else if(op_type_id==ID_fixedbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        fixedbvt f(expr.op0());
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_fixedbv)
      {
        // float to double or double to float
        fixedbvt f(expr.op0());
        f.round(to_fixedbv_type(expr_type));
        expr=f.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_floatbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        ieee_floatt f(expr.op0());
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_floatbv)
      {
        // float to double or double to float
        ieee_floatt f(expr.op0());
        f.change_spec(to_floatbv_type(expr_type));
        expr=f.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_bv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_floatbv)
      {
        mp_integer int_value=binary2integer(
          id2string(value), false);
        new_expr.set(ID_value, integer2binary(int_value, expr_width));
        expr.swap(new_expr);
        return false;
      }
    }
  }
  else if(operand.id()==ID_typecast) // typecast of typecast
  {
    if(operand.operands().size()==1 &&
       op_type_id==expr_type_id &&
       (expr_type_id==ID_unsignedbv || expr_type_id==ID_signedbv) &&
       expr_width<=op_width)
    {
      exprt tmp;
      tmp.swap(expr.op0().op0());
      expr.op0().swap(tmp);
      return false;
    }
  }

  // propagate type casts into arithmetic operators

  if((op_type_id==ID_unsignedbv || op_type_id==ID_signedbv) &&
     (expr_type_id==ID_unsignedbv || expr_type_id==ID_signedbv) &&
     (operand.id()==ID_plus || operand.id()==ID_minus ||
      operand.id()==ID_unary_minus || operand.id()==ID_mult) &&
     expr_width<=op_width)
  {
    exprt new_expr;
    new_expr.swap(expr.op0());
    new_expr.type()=expr.type();

    Forall_operands(it, new_expr)
    {
      it->make_typecast(expr.type());
      simplify_rec(*it); // recursive call
    }

    expr.swap(new_expr);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_dereference(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &pointer=expr.op0();

  if(pointer.type().id()!=ID_pointer) return true;
  
  if(pointer.id()==ID_address_of)
  {
    if(pointer.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(pointer.op0());
      expr.swap(tmp);
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_address_of_arg

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

    if(expr.op0().is_zero()) // NULL
    {
      address=0;
      return true;
    }
  }
  
  return false;
}

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
        
        step_size=pointer_offset_size(ns, expr.type());
        
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
          mp_integer offset=member_offset(ns, struct_type, member);
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

  if(ptr.type().id()!=ID_pointer) return true;
  
  if(ptr.id()==ID_address_of)
  {
    if(ptr.operands().size()!=1) return true;

    mp_integer offset=compute_pointer_offset(ns, ptr.op0());

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
      pointer_offset_size(ns, pointer_type.subtype());
    
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

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_multiplication

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_multiplication(exprt &expr)
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

Function: simplify_exprt::simplify_division

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_division(exprt &expr)
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
      fixedbvt f0(expr.op0());
      fixedbvt f1(expr.op1());
      if(!f1.is_zero())
      {
        f0/=f1;
        expr=f0.to_expr();
        return false;
      }
    }
  }
  else if(expr_type.id()==ID_floatbv)
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
      ieee_floatt f0(expr.op0());
      ieee_floatt f1(expr.op1());
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

Function: simplify_exprt::simplify_modulo

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_modulo(exprt &expr)
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

Function: simplify_exprt::simplify_addition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_addition(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  bool result=true;

  exprt::operandst &operands=expr.operands();
  
  assert(expr.id()==ID_plus);
  
  // count constants
  unsigned count=0;
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
  
  // delete non-float zeros 
  // (for float's the result of 0.0 + (-0.0) may not be -0.0 in std rounding)
  for(exprt::operandst::iterator
      it=operands.begin();
      it!=operands.end();
      /* no it++ */)
  {
    if(is_number(it->type()) && 
       it->is_zero() &&
       it->type().id()!=ID_floatbv)
    {
      it=operands.erase(it);
      result=false;
    }
    else
      it++;
  }

  if(operands.size()==0)
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

Function: simplify_exprt::simplify_subtraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_subtraction(exprt &expr)
{
  if(!is_number(expr.type()) &&
     expr.type().id()!=ID_pointer)
    return true;

  exprt::operandst &operands=expr.operands();

  assert(expr.id()==ID_minus);

  if(operands.size()!=2)
    return true;
  
  if(is_number(expr.type()) &&
     is_number(operands.front().type()) &&
     is_number(operands.back().type()))
  {
    exprt tmp2(ID_unary_minus, expr.type());
    tmp2.move_to_operands(operands.back());
    simplify_node(tmp2);

    exprt tmp(ID_plus, expr.type());
    tmp.move_to_operands(operands.front());
    tmp.move_to_operands(tmp2);

    expr.swap(tmp);
    simplify_node(expr);

    return false;
  }
  else if(expr.type().id()==ID_pointer &&
          is_number(operands.back().type()))
  {
    // pointer arithmetic
    exprt tmp2(ID_unary_minus, operands.back().type());
    tmp2.move_to_operands(operands.back());
    simplify_node(tmp2);

    exprt tmp(ID_plus, expr.type());
    tmp.move_to_operands(operands.front());
    tmp.move_to_operands(tmp2);

    expr.swap(tmp);
    simplify_node(expr);

    return false;
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
          it->make_false();
        else if(it->is_one())
          it->make_true();
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
  
  unsigned width=bv_width(expr.type());
    
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
      
    exprt new_op(ID_constant, expr.type());
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
      
    new_op.set(ID_value, new_value);

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
      if(it->is_zero())
      {
        it=expr.operands().erase(it);
        result=false;
      }
      else
        it++;
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
  
  unsigned width=bv_width(op0_type);

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
    for(unsigned i=0; i<expr.operands().size(); i++)
    {
      exprt &op=expr.operands()[i];
      if(op.is_true() || op.is_false())
      {
        bool value=op.is_true();
        op=exprt(ID_constant, typet(ID_unsignedbv));
        op.type().set(ID_width, 1);
        op.set(ID_value, value?ID_1:ID_0);
      }
    }
    
    // search for neighboring constants to merge
    unsigned i=0;
    
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
      // this is to simulate an arithmetic right shift
      if(distance>=0)
      {
        mp_integer new_value=(distance>=width)?0:value/power(2, distance);

        if(value<0 && new_value==0) new_value=-1;
  
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

Function: simplify_exprt::simplify_if_implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_implies(
  exprt &expr,
  const exprt &cond,
  bool truth,
  bool &new_truth)
{
  if(expr == cond) {
   new_truth = truth;
   return false;
  }

  if(truth && cond.id()==ID_lt && expr.id()==ID_lt)
  {
    if(cond.op0() == expr.op0() &&
	cond.op1().is_constant() &&
	expr.op1().is_constant() &&
	cond.op1().type() == expr.op1().type())
    {
      const irep_idt &type_id = cond.op1().type().id();
      if(type_id==ID_integer || type_id==ID_natural)
      {
	if(string2integer(cond.op1().get_string(ID_value)) >=
	  string2integer(expr.op1().get_string(ID_value)))
	 {
	  new_truth = true;
	  return false;
	 }
      }
      else if(type_id==ID_unsignedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), false) >=
           binary2integer(expr.op1().get_string(ID_value), false))
	 {
	  new_truth = true;
	  return false;
	 }
      }
      else if(type_id==ID_signedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), true) >=
           binary2integer(expr.op1().get_string(ID_value), true))
	 {
	  new_truth = true;
	  return false;
	 }
      }
    }
    if(cond.op1() == expr.op1() &&
	cond.op0().is_constant() &&
	expr.op0().is_constant() &&
	cond.op0().type() == expr.op0().type())
    {
      const irep_idt &type_id = cond.op1().type().id();
      if(type_id==ID_integer || type_id==ID_natural)
      {
	if(string2integer(cond.op1().get_string(ID_value)) <=
           string2integer(expr.op1().get_string(ID_value)))
	 {
	  new_truth = true;
	  return false;
	 }
      }
      else if(type_id==ID_unsignedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), false) <=
           binary2integer(expr.op1().get_string(ID_value), false))
	 {
	  new_truth = true;
	  return false;
	 }
      }
      else if(type_id==ID_signedbv)
      {
	const mp_integer i1, i2;
	if(binary2integer(cond.op1().get_string(ID_value), true) <=
           binary2integer(expr.op1().get_string(ID_value), true))
	 {
	  new_truth = true;
	  return false;
	 }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_recursive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_recursive(
  exprt &expr,
  const exprt &cond,
  bool truth)
{
  if(expr.type().id()==ID_bool)
  {
    bool new_truth;

    if(!simplify_if_implies(expr, cond, truth, new_truth))
    {
      if(new_truth)
      {
	expr.make_true();
	return false;
      }
      else
      {
	expr.make_false();
	return false;
      }
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_recursive(*it, cond, truth) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_conj

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_conj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr.make_true();
      return false;
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_conj(*it, cond) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_disj

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_disj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr == *it)
    {
      expr.make_false();
      return false;
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_disj(*it, cond) && result;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_branch(
  exprt &trueexpr,
  exprt &falseexpr,
  const exprt &cond)
{
  bool tresult = true;
  bool fresult = true;

  if(cond.id()==ID_and)
  {
    tresult = simplify_if_conj(trueexpr, cond) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }
  else if(cond.id()==ID_or)
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_disj(falseexpr, cond) && fresult;
  }
  else
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }

  if(!tresult) simplify_rec(trueexpr);
  if(!fresult) simplify_rec(falseexpr);

  return tresult && fresult;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if_cond(exprt &expr)
{
  bool result = true;
  bool tmp = false;

  while(!tmp)
  {
    tmp = true;

    if(expr.id()==ID_and)
    {
      if(expr.has_operands())
      {
	exprt::operandst &operands = expr.operands();
	for(exprt::operandst::iterator it1 = operands.begin();
	    it1 != operands.end(); it1++)
        {
	  for(exprt::operandst::iterator it2 = operands.begin();
	      it2 != operands.end(); it2++)
          {
	    if(it1 != it2)
	      tmp = simplify_if_recursive(*it1, *it2, true) && tmp;
          }
        }
      }
    }

    if(!tmp) simplify_rec(expr);

    result = tmp && result;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_if(exprt &expr)
{
  exprt::operandst &operands=expr.operands();
  if(operands.size()!=3) return true;

  bool result = true;

  exprt &cond=operands[0];
  exprt &truevalue=operands[1];
  exprt &falsevalue=operands[2];

  if(truevalue==falsevalue)
  {
    exprt tmp;
    tmp.swap(truevalue);
    expr.swap(tmp);
    return false;
  }

  if(do_simplify_if)
  {
    if(cond.id()==ID_not)
    {
      exprt tmp;
      tmp.swap(cond.op0());
      cond.swap(tmp);
      truevalue.swap(falsevalue);
    }

    #if 0
    result = simplify_if_cond(cond) && result;
    result = simplify_if_branch(truevalue, falsevalue, cond) && result;
    #endif

    if(expr.type()==bool_typet())
    {
      // a?b:c <-> (a && b) || (!a && c)
    
      if(truevalue.is_true() && falsevalue.is_false())
      {
        // a?1:0 <-> a
        exprt tmp;
        tmp.swap(cond);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false() && falsevalue.is_true())
      {
        // a?0:1 <-> !a
        exprt tmp;
        tmp.swap(cond);
        tmp.make_not();
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_false())
      {
        // a?b:0 <-> a AND b
        and_exprt tmp(cond, truevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_true())
      {
        // a?b:1 <-> !a OR b
        or_exprt tmp(cond, truevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        or_exprt tmp(cond, falsevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false())
      {
        // a?0:b <-> !a && b
        and_exprt tmp(cond, falsevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
    }
  }

  if(cond.is_true())
  {
    exprt tmp;
    tmp.swap(truevalue);
    expr.swap(tmp);
    return false;
  }

  if(cond.is_false())
  {
    exprt tmp;
    tmp.swap(falsevalue);
    expr.swap(tmp);
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_switch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_switch(exprt &expr)
{
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_not(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  exprt &op=expr.op0();

  if(expr.type().id()!=ID_bool ||
     op.type().id()!=ID_bool) return true;
     
  if(op.id()==ID_not) // (not not a) == a
  {
    if(op.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(op.op0());
      expr.swap(tmp);
      return false;
    }
  }
  else if(op.is_false())
  {
    expr.make_true();
    return false;
  }
  else if(op.is_true())
  {
    expr.make_false();
    return false;
  }
  else if(op.id()==ID_and ||
          op.id()==ID_or)
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);

    Forall_operands(it, expr)
    {
      it->make_not();
      simplify_node(*it);
    }
    
    expr.id(expr.id()==ID_and?ID_or:ID_and);

    return false;
  }
  else if(op.id()==ID_notequal) // !(a!=b) <-> a==b
  {
    exprt tmp;
    tmp.swap(op);
    expr.swap(tmp);
    expr.id(ID_equal);
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_boolean(exprt &expr)
{
  if(!expr.has_operands()) return true;

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(expr.id()==ID_implies)
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;
      
    // turn a => b into !a || b

    expr.id(ID_or);
    expr.op0().make_not();
    simplify_node(expr.op0());
    simplify_node(expr);
    return false;
  }
  else if(expr.id()=="<=>")
  {
    if(operands.size()!=2 ||
       operands.front().type().id()!=ID_bool ||
       operands.back().type().id()!=ID_bool)
      return true;

    if(operands.front().is_false())
    {
      expr.id(ID_not);
      operands.erase(operands.begin());
      return false;
    }
    else if(operands.front().is_true())
    {
      exprt tmp(operands.back());
      expr.swap(tmp);
      return false;
    }
    else if(operands.back().is_false())
    {
      expr.id(ID_not);
      operands.erase(++operands.begin());
      return false;
    }
    else if(operands.back().is_true())
    {
      exprt tmp(operands.front());
      expr.swap(tmp);
      return false;
    }    
  }
  else if(expr.id()==ID_or ||
          expr.id()==ID_and ||
          expr.id()==ID_xor)
  {
    if(operands.size()==0) return true;

    bool result=true;

    exprt::operandst::const_iterator last;
    bool last_set=false;

    for(exprt::operandst::iterator it=operands.begin();
        it!=operands.end();)
    {
      if(it->type().id()!=ID_bool) return true;

      bool is_true=it->is_true();
      bool is_false=it->is_false();

      if(expr.id()==ID_and && is_false)
      {
        expr.make_false();
        return false;
      }
      else if(expr.id()==ID_or && is_true)
      {
        expr.make_true();
        return false;
      }

      bool erase;

      if(expr.id()==ID_and)
        erase=is_true;
      else
        erase=is_false;

      if(last_set && *it==*last &&
         (expr.id()==ID_or || expr.id()==ID_and))
        erase=true; // erase duplicate operands

      if(erase)
      {
        it=operands.erase(it);
        result=false;
      }
      else
      {
        last=it;
        last_set=true;
        it++;
      }
    }
    
    // search for a and !a
    if(expr.id()==ID_and || expr.id()==ID_or)
    {
      // first gather all the a's with !a

      std::set<exprt> expr_set;

      forall_operands(it, expr)
        if(it->id()==ID_not &&
           it->operands().size()==1 &&
           it->type().id()==ID_bool)
          expr_set.insert(it->op0());

      // now search for a

      forall_operands(it, expr)
        if(expr_set.find(*it)!=expr_set.end())
        {
          expr.make_bool(expr.id()==ID_or);
          return false;
        }
    }

    if(operands.size()==0)
    {
      if(expr.id()==ID_and)
        expr.make_true();
      else
        expr.make_false();

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

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_bitnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_bitnot(exprt &expr)
{
  if(!expr.has_operands()) return true;

  exprt::operandst &operands=expr.operands();

  if(operands.size()!=1) return true;

  exprt &op=operands.front();

  if(expr.type().id()==ID_bv ||
     expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(op.type()==expr.type())
    {
      if(op.id()==ID_constant)
      {
        std::string value=op.get_string(ID_value);

        for(unsigned i=0; i<value.size(); i++)
          value[i]=(value[i]=='0')?'1':'0';

        exprt tmp(ID_constant, op.type());
        tmp.set(ID_value, value);
        expr.swap(tmp);
        return false;
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::get_values(
  const exprt &expr,
  value_listt &value_list)
{
  if(expr.is_constant())
  {
    mp_integer int_value;
    if(to_integer(expr, int_value))
      return true;

    value_list.insert(int_value);

    return false;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      return true;

    return get_values(expr.op1(), value_list) ||
           get_values(expr.operands().back(), value_list);
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_address_of(exprt &expr)
{
  assert(expr.type().id()==ID_bool);
  assert(expr.operands().size()==2);
  assert(expr.op0().id()==ID_address_of);
  assert(expr.op1().id()==ID_address_of);
  assert(expr.id()==ID_equal || expr.id()==ID_notequal);

  if(expr.op0().operands().size()!=1) return true;
  if(expr.op1().operands().size()!=1) return true;
  
  if(expr.op0().op0().id()==ID_symbol &&
     expr.op1().op0().id()==ID_symbol)
  {
    bool equal=
       expr.op0().op0().get(ID_identifier)==
       expr.op1().op0().get(ID_identifier);
       
    expr.make_bool(expr.id()==ID_equal?equal:!equal);
    
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality

  Inputs:

 Outputs:

 Purpose: simplifies inequalities !=, <=, <, >=, >, and also ==

\*******************************************************************/

bool simplify_exprt::simplify_inequality(exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(operands.size()!=2) return true;
  
  // types must match
  if(!base_type_eq(expr.op0().type(), expr.op1().type(), ns))
    return true;
    
  // see if we are comparing pointers that are address_of
  if(expr.op0().id()==ID_address_of &&
     expr.op1().id()==ID_address_of &&
     (expr.id()==ID_equal || expr.id()==ID_notequal))
    return simplify_inequality_address_of(expr);

  // first see if we compare to a constant
  
  bool op0_is_const=expr.op0().is_constant();
  bool op1_is_const=expr.op1().is_constant();
  
  exprt tmp0=expr.op0();
  exprt tmp1=expr.op1();
  ns.follow_symbol(tmp0.type());
  ns.follow_symbol(tmp1.type());

  // are _both_ constant?  
  if(op0_is_const && op1_is_const)
  {
    if(tmp0.id()==ID_bool)
    {
      bool v0=tmp0.is_true();
      bool v1=tmp1.is_true();

      if(expr.id()==ID_equal)
      {
        expr.make_bool(v0==v1);
        return false;
      }
      else if(expr.id()==ID_notequal)
      {
        expr.make_bool(v0!=v1);
        return false;
      }
    }
    else if(tmp0.type().id()==ID_fixedbv)
    {
      fixedbvt f0(tmp0);
      fixedbvt f1(tmp1);

      if(expr.id()==ID_notequal)
        expr.make_bool(f0!=f1);
      else if(expr.id()==ID_equal)
        expr.make_bool(f0==f1);
      else if(expr.id()==ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        assert(false);
    
      return false;
    }
    else if(tmp0.type().id()==ID_floatbv)
    {
      ieee_floatt f0(tmp0);
      ieee_floatt f1(tmp1);

      if(expr.id()==ID_notequal)
        expr.make_bool(f0!=f1);
      else if(expr.id()==ID_equal)
        expr.make_bool(f0==f1);
      else if(expr.id()==ID_ge)
        expr.make_bool(f0>=f1);
      else if(expr.id()==ID_le)
        expr.make_bool(f0<=f1);
      else if(expr.id()==ID_gt)
        expr.make_bool(f0>f1);
      else if(expr.id()==ID_lt)
        expr.make_bool(f0<f1);
      else
        assert(false);
    
      return false;
    }
    else if(tmp0.type().id()==ID_rational)
    {
      rationalt r0, r1;

      if(to_rational(tmp0, r0))
        return true;

      if(to_rational(tmp1, r1))
        return true;

      if(expr.id()==ID_notequal)
        expr.make_bool(r0!=r1);
      else if(expr.id()==ID_equal)
        expr.make_bool(r0==r1);
      else if(expr.id()==ID_ge)
        expr.make_bool(r0>=r1);
      else if(expr.id()==ID_le)
        expr.make_bool(r0<=r1);
      else if(expr.id()==ID_gt)
        expr.make_bool(r0>r1);
      else if(expr.id()==ID_lt)
        expr.make_bool(r0<r1);
      else
        assert(false);

      return false;
    }
    else
    {
      mp_integer v0, v1;
      
      if(to_integer(tmp0, v0))
        return true;

      if(to_integer(tmp1, v1))
        return true;
      
      if(expr.id()==ID_notequal)
        expr.make_bool(v0!=v1);
      else if(expr.id()==ID_equal)
        expr.make_bool(v0==v1);
      else if(expr.id()==ID_ge)
        expr.make_bool(v0>=v1);
      else if(expr.id()==ID_le)
        expr.make_bool(v0<=v1);
      else if(expr.id()==ID_gt)
        expr.make_bool(v0>v1);
      else if(expr.id()==ID_lt)
        expr.make_bool(v0<v1);
      else
        assert(false);

      return false;
    }
  }
  else if(op0_is_const)
  {
    // we want the constant on the RHS

    if(expr.id()==ID_ge)
      expr.id(ID_le);
    else if(expr.id()==ID_le)
      expr.id(ID_ge);
    else if(expr.id()==ID_gt)
      expr.id(ID_lt);
    else if(expr.id()==ID_lt)
      expr.id(ID_gt);
    
    expr.op0().swap(expr.op1());
    
    // one is constant
    simplify_inequality_constant(expr);
    return false;
  }
  else if(op1_is_const)
  {
    // one is constant
    return simplify_inequality_constant(expr); 
  }
  else
  {
    // both are not constant
    return simplify_inequality_not_constant(expr);
  }
    
  assert(false);
  return false;
}

/*******************************************************************\

Function: simplify_exprt::eliminate_common_addends

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::eliminate_common_addends(
  exprt &op0,
  exprt &op1)
{
  // we can't eliminate zeros
  if(op0.is_zero() || op1.is_zero()) return true;
  
  if(op0.id()==ID_plus)
  {
    bool result=true;

    Forall_operands(it, op0)
      if(!eliminate_common_addends(*it, op1))
        result=false;

    return result;
  }
  else if(op1.id()==ID_plus)
  {
    bool result=true;

    Forall_operands(it, op1)
      if(!eliminate_common_addends(op0, *it))
        result=false;
      
    return result;
  }
  else if(op0==op1)
  {
    // elimination!
    op0=gen_zero(op0.type());
    op1=gen_zero(op1.type());
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_not_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_not_constant(exprt &expr)
{
  exprt::operandst &operands=expr.operands();
  
  // pretty much all of the simplifications below are unsound
  // for IEEE float because of NaN!
  
  if(ns.follow(expr.op0().type()).id()==ID_floatbv)
    return true;
  
  // eliminate strict inequalities
  if(expr.id()==ID_notequal)
  {
    expr.id(ID_equal);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_not(expr);
    return false;
  }
  else if(expr.id()==ID_gt)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_not(expr);
    return false;
  }
  else if(expr.id()==ID_lt)
  {
    expr.id(ID_ge);
    simplify_inequality_not_constant(expr);
    expr.make_not();
    simplify_not(expr);
    return false;
  }
  else if(expr.id()==ID_le)
  {
    expr.id(ID_ge);
    // swap operands
    expr.op0().swap(expr.op1());
    simplify_inequality_not_constant(expr);
    return false;
  }

  // now we only have >=, =

  assert(expr.id()==ID_ge || expr.id()==ID_equal);

  // syntactically equal?

  if(operands.front()==operands.back())
  {
    expr.make_true();
    return false;
  }

  // try constants

  value_listt values0, values1;

  bool ok0=!get_values(expr.op0(), values0);
  bool ok1=!get_values(expr.op1(), values1);

  if(ok0 && ok1)
  {
    bool first=true;
    bool result=false; // dummy initialization to prevent warning
    bool ok=true;

    // compare possible values

    forall_value_list(it0, values0)
      forall_value_list(it1, values1)
      {
        bool tmp;
        const mp_integer &int_value0=*it0;
        const mp_integer &int_value1=*it1;

        if(expr.id()==ID_ge)
          tmp=(int_value0 >= int_value1);
        else if(expr.id()==ID_equal)
          tmp=(int_value0 == int_value1);
        else
          assert(0);

        if(first)
        {
          result=tmp;
          first=false;
        }
        else if(result!=tmp)
        {
          ok=false;
          break;
        }
      }

    if(ok)
    {
      expr.make_bool(result);
      return false;
    }
  }
  
  // see if we can eliminate common addends on both sides
  // on bit-vectors, this is only sound on '='
  if(expr.id()==ID_equal)
    if(!eliminate_common_addends(expr.op0(), expr.op1()))
    {
      // remove zeros
      simplify_node(expr.op0());
      simplify_node(expr.op1());
      simplify_inequality(expr);
      return false;
    }
  
  return true;
}  

/*******************************************************************\

Function: simplify_exprt::simplify_inequality_constant

  Inputs: an inequality with a constant on the RHS

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_inequality_constant(exprt &expr)
{
  // the constant is always on the RHS
  assert(expr.op1().is_constant());

  // do we deal with pointers?
  if(expr.op1().type().id()==ID_pointer)
  {
    if(expr.id()==ID_notequal)
    {
      expr.id(ID_equal);
      simplify_inequality_constant(expr);
      expr.make_not();
      simplify_not(expr);
      return false;
    }
  
    // very special case for pointers
    if(expr.id()==ID_equal &&
       expr.op1().is_constant() &&
       expr.op1().get(ID_value)==ID_NULL)
    {
      // the address of an object is never NULL
    
      if(expr.op0().id()==ID_address_of && 
         expr.op0().operands().size()==1)
      {
        if(expr.op0().op0().id()==ID_symbol ||
           expr.op0().op0().id()==ID_member ||
           expr.op0().op0().id()==ID_index)
        {
          expr.make_false();
          return false;
        }
      }
      else if(expr.op0().id()==ID_typecast &&
              expr.op0().operands().size()==1 &&
              expr.op0().type().id()==ID_pointer)
      {
        // (type)ptr == NULL -> ptr == NULL
        // note that 'ptr' may be an integer
        exprt op=expr.op0().op0();
        expr.op0().swap(op);
        expr.op1()=gen_zero(expr.op0().type());
        simplify_inequality(expr); // do again!
        return false;
      }
    }

    // all we are doing with pointers
    return true;
  }
  
  // is it a separation predicate?
  
  if(expr.op0().id()==ID_plus)
  {
    // see if there is a constant in the sum
    
    if(expr.id()==ID_equal || expr.id()==ID_notequal)
    {
      mp_integer constant=0;
      bool changed=false;
      
      Forall_operands(it, expr.op0())
      {
        if(it->is_constant())
        {
          mp_integer i;
          if(!to_integer(*it, i))
          {
            constant+=i;
            *it=gen_zero(it->type());
            changed=true;
          }
        }
      }
      
      if(changed)
      {
        // adjust constant
        mp_integer i;
        to_integer(expr.op1(), i);
        i-=constant;
        expr.op1()=from_integer(i, expr.op1().type());

        simplify_addition(expr.op0());
        simplify_inequality(expr);
        return false;
      }
    }
  }

  // is the constant zero?

  if(expr.op1().is_zero())
  {
    if(expr.id()==ID_ge &&
       expr.op0().type().id()==ID_unsignedbv)
    {
      // zero is always smaller or equal something unsigned
      expr.make_true();
      return false;
    }

    exprt &operand=expr.op0();

    if(expr.id()==ID_equal)
    {
      // rules below do not hold for >=
      if(operand.id()==ID_unary_minus)
      {
        if(operand.operands().size()!=1) return true;
        exprt tmp;
        tmp.swap(operand.op0());
        operand.swap(tmp);
        return false;
      }
      else if(operand.id()==ID_plus)
      {
        // simplify a+-b=0 to a=b

        if(operand.operands().size()==2)
        {
          // if we have -b+a=0, make that a+(-b)=0

          if(operand.op0().id()==ID_unary_minus)
            operand.op0().swap(operand.op1());

          if(operand.op1().id()==ID_unary_minus &&
             operand.op1().operands().size()==1)
          {
            exprt tmp(expr.id(), expr.type());
            tmp.operands().resize(2);
            tmp.op0().swap(operand.op0());
            tmp.op1().swap(operand.op1().op0());
            expr.swap(tmp);
            return false;
          }
        }
      }
    }
  }

  // are we comparing with a typecast from bool?
  if(expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     expr.op0().op0().type().id()==ID_bool)
  {
    // we re-write (TYPE)boolean == 0 -> !boolean
    if(expr.op1().is_zero() && expr.id()==ID_equal)
    {
      exprt tmp=expr.op0().op0();
      tmp.make_not();
      expr.swap(tmp);
      return false;
    }

    // we re-write (TYPE)boolean != 0 -> boolean
    if(expr.op1().is_zero() && expr.id()==ID_notequal)
    {
      exprt tmp=expr.op0().op0();
      expr.swap(tmp);
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_ieee_float_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_ieee_float_relation(exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(operands.size()!=2) return true;

  // types must match
  if(expr.op0().type()!=expr.op1().type())
    return true;

  if(expr.op0().type().id()!=ID_floatbv)
    return true;

  // first see if we compare to a constant

  if(expr.op0().is_constant() &&
     expr.op1().is_constant())
  {
    ieee_floatt f0(expr.op0());
    ieee_floatt f1(expr.op1());

    if(expr.id()==ID_ieee_float_notequal)
      expr.make_bool(ieee_not_equal(f0, f1));
    else if(expr.id()==ID_ieee_float_equal)
      expr.make_bool(ieee_equal(f0, f1));
    else
      assert(false);
  
    return false;
  }

  if(expr.op0()==expr.op1())
  {
    // x!=x is the same as saying isnan(op)
    exprt isnan(ID_isnan, bool_typet());
    isnan.copy_to_operands(expr.op0());

    if(expr.id()==ID_ieee_float_notequal)
    {
    }
    else if(expr.id()==ID_ieee_float_equal)
      isnan.make_not();
    else
      assert(false);
  
    expr.swap(isnan);
    return false;
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_lambda

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_lambda(exprt &expr)
{
  bool result=true;

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_with(exprt &expr)
{
  bool result=true;
  
  if((expr.operands().size()%2)!=1)
    return true;
    
  const typet op0_type=ns.follow(expr.op0().type());

  // now look at first operand
  
  if(op0_type.id()==ID_struct)
  {
    if(expr.op0().id()==ID_struct ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        const irep_idt &component_name=
          expr.op1().get(ID_component_name);

        if(!to_struct_type(expr.op0().type()).
           has_component(component_name))
          return result;

        unsigned number=to_struct_type(expr.op0().type()).
           component_number(component_name);

        expr.op0().operands()[number].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_array)
  {
    if(expr.op0().id()==ID_array ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        mp_integer i;
        
        if(to_integer(expr.op1(), i))
          break;
          
        if(i<0 || i>=expr.op0().operands().size())
          break;
          
        if(!expr.op2().is_constant())
          break;

        expr.op0().operands()[integer2long(i)].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }

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

Function: simplify_exprt::simplify_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_index(index_exprt &expr)
{
  bool result=true;

  // extra arithmetic optimizations
  const exprt &offset=expr.index();
  const exprt &array=expr.array();

  if(offset.id()==ID_div &&
     offset.operands().size()==2)
  {
    if(offset.op0().id()==ID_mult &&
       offset.op0().operands().size()==2 &&
       offset.op0().op1()==offset.op1())
    {
      exprt tmp=offset.op0().op0();
      expr.op1()=tmp;
      result=false;
    }
    else if(offset.op0().id()==ID_mult &&
            offset.op0().operands().size()==2 &&
            offset.op0().op0()==offset.op1())
    {
      exprt tmp=offset.op0().op1();
      expr.op1()=tmp;
      result=false;
    }
  }

  if(array.id()==ID_lambda)
  {
    // simplify (lambda i: e)(x) to e[i/x]

    const exprt &lambda_expr=array;

    if(lambda_expr.operands().size()!=2) return true;

    if(expr.op1().type()==lambda_expr.op0().type())
    {
      exprt tmp=lambda_expr.op1();
      replace_expr(lambda_expr.op0(), expr.op1(), tmp);
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_with)
  {
    const exprt &with_expr=array;

    if(with_expr.operands().size()!=3) return true;
    
    if(with_expr.op1()==expr.op1())
    {
      // simplify (e with [i:=v])[i] to v
      exprt tmp=with_expr.op2();
      expr.swap(tmp);
      return false;
    }
    else
    {
      // turn (a with i:=x)[j] into (i==j)?x:a[j]
      // watch out that the type of i and j might be different
      equal_exprt equality_expr(expr.op1(), with_expr.op1());
      
      if(equality_expr.lhs().type()!=equality_expr.rhs().type())
        equality_expr.rhs().make_typecast(equality_expr.lhs().type());

      simplify_inequality(equality_expr);
      
      index_exprt new_index_expr;
      new_index_expr.type()=expr.type();
      new_index_expr.array()=with_expr.op0();
      new_index_expr.index()=expr.op1();

      simplify_index(new_index_expr); // recursive call

      exprt if_expr(ID_if, expr.type());
      if_expr.reserve_operands(3);
      if_expr.move_to_operands(equality_expr);
      if_expr.copy_to_operands(with_expr.op2());
      if_expr.move_to_operands(new_index_expr);

      simplify_if(if_expr);

      expr.swap(if_expr);

      return false;
    }
  }
  else if(array.id()==ID_constant ||
          array.id()==ID_array)
  {
    mp_integer i;
    
    if(to_integer(expr.op1(), i))
    {
    }
    else if(i<0 || i>=array.operands().size())
    {
      // out of bounds
    }
    else
    {
      // ok
      exprt tmp=array.operands()[integer2long(i)];
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_string_constant)
  {
    mp_integer i;
    
    const irep_idt &value=array.get(ID_value);
  
    if(to_integer(expr.op1(), i))
    {
    }
    else if(i<0 || i>value.size())
    {
      // out of bounds
    }
    else
    {
      // terminating zero?
      char v=(i==value.size())?0:value[integer2long(i)];
      exprt tmp=from_integer(v, expr.type());
      expr.swap(tmp);
      return false;
    }
  }
  else if(array.id()==ID_array_of)
  {
    if(array.operands().size()==1)
    {
      exprt tmp=array.op0();
      expr.swap(tmp);
      return false;
    }
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_object(exprt &expr)
{
  if(expr.id()==ID_plus)
  {
    if(expr.type().id()==ID_pointer)
    {
      // kill integers from sum
      for(unsigned i=0; i<expr.operands().size(); i++)
        if(ns.follow(expr.operands()[i].type()).id()==ID_pointer)
        {
          exprt tmp=expr.operands()[i];
          expr.swap(tmp);
          simplify_object(expr);
          return false;
        }
    }
  }
  else if(expr.id()==ID_typecast)
  {
    const typet &op_type=ns.follow(expr.op0().type());
  
    assert(expr.operands().size()==1);
    
    if(op_type.id()==ID_pointer)
    {
      // cast from pointer to pointer
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
      simplify_object(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
    {
      // cast from integer to pointer

      // We do a bit of special treatment for (TYPE *)(a+(int)&o),
      // which is re-written to '&o'.

      exprt tmp=expr.op0();
      if(tmp.id()==ID_plus && tmp.operands().size()==2)
      {
        if(tmp.op0().id()==ID_typecast &&
           tmp.op0().operands().size()==1 &&
           tmp.op0().op0().id()==ID_address_of)
        {
          expr=tmp.op0().op0();
          return false;
        }
        else if(tmp.op1().id()==ID_typecast &&
                tmp.op1().operands().size()==1 &&
                tmp.op1().op0().id()==ID_address_of)
        {
          expr=tmp.op1().op0();
          return false;
        }
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_pointer_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_pointer_object(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  return simplify_object(op);
}

/*******************************************************************\

Function: simplify_exprt::simplify_dynamic_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_dynamic_object(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  return simplify_object(op);
}

/*******************************************************************\

Function: simplify_exprt::objects_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt simplify_exprt::objects_equal(const exprt &a, const exprt &b)
{
  if(a==b) return tvt(true);

  if(a.id()==ID_address_of && b.id()==ID_address_of &&
     a.operands().size()==1 && b.operands().size()==1)
    return objects_equal_address_of(a.op0(), b.op0());

  if(a.id()==ID_constant && b.id()==ID_constant &&
     a.get(ID_value)==ID_NULL && b.get(ID_value)==ID_NULL)
    return tvt(true);

  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: simplify_exprt::objects_equal_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt simplify_exprt::objects_equal_address_of(const exprt &a, const exprt &b)
{
  if(a==b) return tvt(true);

  if(a.id()==ID_symbol && b.id()==ID_symbol)
  {
    if(a.get(ID_identifier)==b.get(ID_identifier))
      return tvt(true);
  }
  else if(a.id()==ID_index && b.id()==ID_index)
  {
    if(a.operands().size()==2 && b.operands().size()==2)
      return objects_equal_address_of(a.op0(), b.op0());
  }
  else if(a.id()==ID_member && b.id()==ID_member)
  {
    if(a.operands().size()==1 && b.operands().size()==1)
      return objects_equal_address_of(a.op0(), b.op0());
  }

  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: simplify_exprt::simplify_same_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_same_object(exprt &expr)
{
  if(expr.operands().size()!=2) return true;

  bool result=true;

  if(!simplify_object(expr.op0())) result=false;
  if(!simplify_object(expr.op1())) result=false;
  
  tvt res=objects_equal(expr.op0(), expr.op1());

  if(res.is_true())
  {
    expr.make_true();
    return false;
  }
  else if(res.is_false())
  {
    expr.make_false();
    return false;
  }

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify_dynamic_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_dynamic_size(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  return simplify_object(op);
}

/*******************************************************************\

Function: simplify_exprt::simplify_valid_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_valid_object(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
  
  exprt &op=expr.op0();
  
  return simplify_object(op);
}

/*******************************************************************\

Function: simplify_exprt::simplify_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_member(member_exprt &expr)
{
  if(expr.operands().size()!=1) return true;

  const irep_idt &component_name=expr.get_component_name();

  exprt &op=expr.op0();
  const typet &op_type=ns.follow(op.type());

  if(op.id()==ID_with)
  {
    if(op.operands().size()>=3)
    {
      exprt::operandst &operands=op.operands();

      while(operands.size()>1)
      {
        exprt &op1=operands[operands.size()-2];
        exprt &op2=operands[operands.size()-1];

        if(op1.get(ID_component_name)==component_name)
        {
          // found it!
          exprt tmp;
          tmp.swap(op2);
          expr.swap(tmp);
          return false;
        }
        else // something else, get rid of it
          operands.resize(operands.size()-2);
      }
      
      if(op.operands().size()==1)
      {
        exprt tmp;
        tmp.swap(op.op0());
        op.swap(tmp);
        // do this recursively
        simplify_member(expr);
      }

      return false;      
    }
  }
  else if(op.id()==ID_struct ||
          op.id()==ID_constant)
  {
    if(op_type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(op_type);
      if(struct_type.has_component(component_name))
      {
        unsigned number=struct_type.component_number(component_name);
        exprt tmp;
        tmp.swap(op.operands()[number]);
        expr.swap(tmp);
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

 Purpose:

\*******************************************************************/

// The entries
//  { "+",      "floatbv"    },
//  { "*",      "floatbv"    },
// are deliberately missing, as FP-addition and multiplication
// aren't associative

struct saj_tablet
{
  const char *id;
  const char *type_id;
} const saj_table[]=
{
  { "+",      "integer"    },
  { "+",      "natural"    },
  { "+",      "real"       },
  { "+",      "complex"    },
  { "+",      "rational"   },
  { "+",      "unsignedbv" },
  { "+",      "signedbv"   },
  { "+",      "fixedbv"    },
  { "+",      "pointer"    },
  { "*",      "integer"    },
  { "*",      "natural"    },
  { "*",      "real"       },
  { "*",      "complex"    },
  { "*",      "rational"   },
  { "*",      "unsignedbv" },
  { "*",      "signedbv"   },
  { "*",      "fixedbv"    },
  { "and",    "bool"       },
  { "or",     "bool"       },
  { "xor",    "bool"       },
  { "bitand", "unsignedbv" },
  { "bitand", "signedbv"   },
  { "bitand", "floatbv"    },
  { "bitand", "fixedbv"    },
  { "bitor",  "unsignedbv" },
  { "bitor",  "signedbv"   },
  { "bitor",  "floatbv"    },
  { "bitor",  "fixedbv"    },
  { "bitxor", "unsignedbv" },
  { "bitxor", "signedbv"   },
  { "bitxor", "floatbv"    },
  { "bitxor", "fixedbv"    },
  { NULL,     NULL         }
};

bool sort_and_join(const irep_idt &id, const irep_idt &type_id)
{
  for(unsigned i=0; saj_table[i].id!=NULL; i++)
    if(id==saj_table[i].id &&
       type_id==saj_table[i].type_id)
      return true;

  return false;
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

  if(!::sort_and_join(expr.id(), expr.type().id()))
    return true;

  // check operand types

  forall_operands(it, expr)
    if(!::sort_and_join(expr.id(), it->type().id()))
      return true;

  // join expressions

  for(unsigned i=0; i<expr.operands().size();)
  {
    if(expr.operands()[i].id()==expr.id())
    {
      unsigned no_joined=expr.operands()[i].operands().size();

      expr.operands().insert(expr.operands().begin()+i+1,
        expr.operands()[i].operands().begin(), 
        expr.operands()[i].operands().end());

      expr.operands().erase(expr.operands().begin()+i);

      i+=no_joined;

      result=false;
    }
    else
      i++;
  }

  // sort it

  result=sort_operands(expr.operands()) && result;

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
    unsigned width=bv_width(op0_type);
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

Function:

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
      fixedbvt f(expr.op0());
      f.negate();
      expr=f.to_expr();
      return false;
    }
    else if(type_id==ID_floatbv)
    {
      ieee_floatt f(expr.op0());
      f.negate();
      expr=f.to_expr();
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_node(exprt &expr)
{
  if(!expr.has_operands()) return true;

  //#define DEBUGX

  #ifdef DEBUGX
  exprt old(expr);
  #endif

  bool result=true;

  result=sort_and_join(expr) && result;

  if(expr.id()==ID_typecast)
    result=simplify_typecast(expr) && result;
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_gt    || expr.id()==ID_lt ||
          expr.id()==ID_ge    || expr.id()==ID_le)
    result=simplify_inequality(expr) && result;
  else if(expr.id()==ID_if)
    result=simplify_if(expr) && result;
  else if(expr.id()==ID_lambda)
    result=simplify_lambda(expr) && result;
  else if(expr.id()==ID_with)
    result=simplify_with(expr) && result;
  else if(expr.id()==ID_index)
    result=simplify_index(to_index_expr(expr)) && result;
  else if(expr.id()==ID_member)
    result=simplify_member(to_member_expr(expr)) && result;
  else if(expr.id()==ID_pointer_object)
    result=simplify_pointer_object(expr) && result;
  else if(expr.id()==ID_same_object)
    result=simplify_same_object(expr) && result;
  else if(expr.id()==ID_dynamic_object)
    result=simplify_dynamic_object(expr) && result;
  else if(expr.id()=="dynamic_size")
    result=simplify_dynamic_size(expr) && result;
  else if(expr.id()=="valid_object")
    result=simplify_valid_object(expr) && result;
  else if(expr.id()==ID_switch)
    result=simplify_switch(expr) && result;
  else if(expr.id()==ID_div)
    result=simplify_division(expr) && result;
  else if(expr.id()==ID_mod)
    result=simplify_modulo(expr) && result;
  else if(expr.id()==ID_bitnot)
    result=simplify_bitnot(expr) && result;
  else if(expr.id()==ID_bitnot ||
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor)
    result=simplify_bitwise(expr) && result;
  else if(expr.id()==ID_ashr || expr.id()==ID_lshr || expr.id()==ID_shl)
    result=simplify_shifts(expr) && result;
  else if(expr.id()==ID_plus)
    result=simplify_addition(expr) && result;
  else if(expr.id()==ID_minus)
    result=simplify_subtraction(expr) && result;
  else if(expr.id()==ID_mult)
    result=simplify_multiplication(expr) && result;
  else if(expr.id()==ID_unary_minus)
    result=simplify_unary_minus(expr) && result;
  else if(expr.id()==ID_unary_plus)
  {
    if(expr.operands().size()==1)
    {
      // simply remove, this is always 'nop'
      expr=expr.op0();
      result=false;
    }
  }
  else if(expr.id()==ID_not)
    result=simplify_not(expr) && result;
  else if(expr.id()==ID_implies || expr.id()=="<=>" ||
          expr.id()==ID_or      || expr.id()==ID_xor ||
          expr.id()==ID_and)
    result=simplify_boolean(expr) && result;
  else if(expr.id()==ID_comma)
  {
    if(expr.operands().size()!=0)
    {
      exprt tmp;
      tmp.swap(expr.operands()[expr.operands().size()-1]);
      expr.swap(tmp);
      result=false;
    }
  }
  else if(expr.id()==ID_dereference)
    result=simplify_dereference(expr) && result;
  else if(expr.id()==ID_address_of)
    result=simplify_address_of(expr) && result;
  else if(expr.id()==ID_pointer_offset)
    result=simplify_pointer_offset(expr) && result;
  else if(expr.id()==ID_extractbit)
    result=simplify_extractbit(expr) && result;
  else if(expr.id()==ID_concatenation)
    result=simplify_concatenation(expr) && result;
  else if(expr.id()==ID_extractbits) 
    result=simplify_extractbits(expr) && result;
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
    result=simplify_ieee_float_relation(expr) && result;

  #ifdef DEBUGX
  if(!result)
  {
    std::cout << "===== " << from_expr(ns, "", old)
              << "\n ---> " << from_expr(ns, "", expr)
              << "\n";
  }
  #endif

  return result;
}

/*******************************************************************\

Function: simplify_exprt::simplify

  Inputs:

 Outputs: returns true if expression unchanged;
          returns false if changed

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_rec(exprt &expr)
{
  // look up in cache
  
  #ifdef USE_CACHE
  std::pair<simplify_expr_cachet::containert::iterator, bool>
    cache_result=simplify_expr_cache.container().
      insert(std::pair<exprt, exprt>(expr, exprt()));
  
  if(!cache_result.second) // found!
  {
    const exprt &new_expr=cache_result.first->second;
  
    if(new_expr.id()==irep_idt())
      return true; // no change
    
    expr=new_expr;
    return false;
  }
  #endif

  bool result=true;
  
  if(expr.id()==ID_address_of)
  {
    // the argument of this expression needs special treatment
  }
  else
  {
    if(expr.has_operands())
      Forall_operands(it, expr)
        if(!simplify_rec(*it)) // recursive call
          result=false;
  }

  if(!simplify_node(expr)) result=false;
  
  #ifdef USE_CACHE
  // save in cache
  if(!result)
    cache_result.first->second=expr;
  #endif

  return result;
}

/*******************************************************************\

Function: simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify(exprt &expr, const namespacet &ns)
{
  simplify_exprt simplify_expr(ns);

  return simplify_expr.simplify(expr);
}
