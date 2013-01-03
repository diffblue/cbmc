/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <pointer_offset_size.h>
#include <arith_tools.h>

#include <pointer-analysis/dereference.h>
#include <pointer-analysis/rewrite_index.h>
#include <langapi/language_util.h>
#include <ansi-c/c_types.h>

#include "goto_symex.h"
#include "renaming_ns.h"
#include "symex_dereference_state.h"

/*******************************************************************\

Function: goto_symext::dereference_rec_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference_rec_address_of(
  exprt &expr,
  statet &state,
  guardt &guard)
{
  // Could be member, could be if, could be index.

  if(expr.id()==ID_member)
    dereference_rec_address_of(
      to_member_expr(expr).struct_op(), state, guard);
  else if(expr.id()==ID_if)
  {
    // the condition is not an address
    dereference_rec(
      to_if_expr(expr).cond(), state, guard, false);

    // add to guard?
    dereference_rec_address_of(
      to_if_expr(expr).true_case(), state, guard);
    dereference_rec_address_of(
      to_if_expr(expr).false_case(), state, guard);
  }
  else if(expr.id()==ID_index)
  {
    // the index is not an address
    dereference_rec(
      to_index_expr(expr).index(), state, guard, false);

    // the array _is_ an address
    dereference_rec_address_of(
      to_index_expr(expr).array(), state, guard);
  }
  else
  {
    // give up and dereference
    
    dereference_rec(expr, state, guard, false);
  }
}

/*******************************************************************\

Function: goto_symext::is_index_member_symbol_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_symext::is_index_member_symbol_if(const exprt &expr)
{
  // Could be member, could be if, could be index.

  if(expr.id()==ID_member)
  {
    return is_index_member_symbol_if(
      to_member_expr(expr).struct_op());
  }
  else if(expr.id()==ID_if)
  {
    return
      is_index_member_symbol_if(to_if_expr(expr).true_case()) &&
      is_index_member_symbol_if(to_if_expr(expr).false_case());
  }
  else if(expr.id()==ID_index)
  {
    return is_index_member_symbol_if(to_index_expr(expr).array());
  }
  else if(expr.id()==ID_symbol)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: goto_symext::address_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_symext::address_arithmetic(
  const exprt &expr,
  statet &state,
  guardt &guard)
{
  if(expr.id()==ID_index)
  {
    exprt base=address_arithmetic(to_index_expr(expr).array(), state, guard);
    exprt sum=exprt(ID_plus, base.type());
    sum.copy_to_operands(base, to_index_expr(expr).index());

    // there could be dereferencing in the index
    dereference_rec(sum.op1(), state, guard, false);
    return sum;
  }
  else if(expr.id()==ID_member)
  {
    const exprt &struct_op=to_member_expr(expr).struct_op();
  
    const typet &type=ns.follow(struct_op.type());
    
    assert(type.id()==ID_struct ||
           type.id()==ID_union);

    exprt base=address_arithmetic(struct_op, state, guard);

    if(type.id()==ID_union)
      return typecast_exprt(base, pointer_typet(expr.type()));

    // do (member_type *)((char *)base)+offset
    typecast_exprt tc1(base, pointer_typet(char_type()));

    mp_integer offset=member_offset(
        ns, to_struct_type(type),
        to_member_expr(expr).get_component_name());

    if(offset>=0)
    {
      exprt sum=exprt(ID_plus, tc1.type());
      sum.copy_to_operands(tc1, from_integer(offset, size_type()));
      
      pointer_typet dest_type;

      if(expr.type().id()==ID_array)
        dest_type.subtype()=expr.type().subtype();
      else
        dest_type.subtype()=expr.type();
    
      return typecast_exprt(sum, dest_type);
    }
  }
  else if(expr.id()==ID_dereference)
  {
    // just grab the pointer, but be wary of further dereferencing
    // in the pointer itself
    exprt tmp=to_dereference_expr(expr).pointer();
    dereference_rec(tmp, state, guard, false);
    return tmp;
  }

  // give up, just dereference
  exprt tmp=expr;
  dereference_rec_address_of(tmp, state, guard);
  
  // turn &array into &array[0]
  if(ns.follow(tmp.type()).id()==ID_array)
  {
    index_exprt tmp2(tmp, gen_zero(index_type()));
    return address_of_exprt(tmp2);
  }
  else
    return address_of_exprt(tmp);
}

/*******************************************************************\

Function: goto_symext::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference_rec(
  exprt &expr,
  statet &state,
  guardt &guard,
  const bool write)
{
  if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference takes one operand";

    exprt tmp1;
    tmp1.swap(expr.op0());
    
    // first make sure there are no dereferences in there
    dereference_rec(tmp1, state, guard, false);

    // we need to set up some elaborate call-backs
    symex_dereference_statet symex_dereference_state(*this, state);
    renaming_nst renaming_ns(ns, state);

    dereferencet dereference(
      renaming_ns,
      new_context,
      options,
      symex_dereference_state);      
    
    // std::cout << "**** " << from_expr(ns, "", tmp1) << std::endl;
    exprt tmp2=dereference.dereference(
      tmp1, guard, write?dereferencet::WRITE:dereferencet::READ);
    //std::cout << "**** " << from_expr(ns, "", tmp2) << std::endl;

    expr.swap(tmp2);
    
    // this may yield a new auto-object
    trigger_auto_object(expr, state);
  }
  else if(expr.id()=="implicit_dereference")
  {
    // old stuff, should be gone
    assert(false);
  }
  else if(expr.id()==ID_index &&
          to_index_expr(expr).array().id()==ID_member &&
          to_array_type(ns.follow(to_index_expr(expr).array().type())).
            size().is_zero())
  {
    // This is an expression of the form x.a[i],
    // where a is a zero-sized array. This gets
    // re-written into *(&x.a+i)
    
    index_exprt index_expr=to_index_expr(expr);
    
    address_of_exprt address_of_expr(index_expr.array());
    address_of_expr.type()=pointer_typet(expr.type());

    dereference_exprt tmp;
    tmp.pointer()=plus_exprt(address_of_expr, index_expr.index());
    tmp.type()=expr.type();
    tmp.location()=expr.location();

    // recursive call
    dereference_rec(tmp, state, guard, write);

    expr.swap(tmp);
  }
  else if(expr.id()==ID_index &&
          expr.operands().size()==2 &&
          expr.op0().type().id()==ID_pointer)
  {
    // old stuff, will go away  
    exprt tmp=rewrite_index(to_index_expr(expr)).pointer();
    dereference_rec(tmp, state, guard, write);
    tmp.swap(expr);
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt &address_of_expr=to_address_of_expr(expr);
    
    exprt &object=address_of_expr.object();

    if(object.id()==ID_dereference)
    {
      // ANSI-C guarantees &*p == p no matter what p is,
      // even if it's complete garbage
      assert(object.operands().size()==1);
      exprt tmp=object.op0();
      expr.swap(tmp);
    
      // do rec. call, as p itself might have dereferencing in it
      dereference_rec(expr, state, guard, false);
    }
    else if(is_index_member_symbol_if(object))
    {
      // simply dereference, this yields "&object"
      dereference_rec_address_of(object, state, guard);
    }
    else
    {
      // fallback: do address arithmetic
      exprt result=address_arithmetic(object, state, guard);
      expr.swap(result);
    }
  }
  else
  {
    Forall_operands(it, expr)
      dereference_rec(*it, state, guard, write);
  }
}

/*******************************************************************\

Function: goto_symext::dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference(
  exprt &expr,
  statet &state,
  const bool write)
{
  // The expression needs to be renamed to level 1
  // in order to distinguish addresses of local variables
  // from different frames. Would be enough to rename
  // symbols whose address is taken.
  assert(!state.call_stack().empty());
  state.rename(expr, ns, goto_symex_statet::L1);

  // start the recursion!
  guardt guard;  
  dereference_rec(expr, state, guard, write);
}
