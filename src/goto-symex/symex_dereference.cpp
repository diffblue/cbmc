/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>
#include <expr_util.h>

#include <pointer-analysis/dereference.h>
#include <pointer-analysis/rewrite_index.h>
#include <langapi/language_util.h>

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
    
    exprt tmp2=dereference.dereference(
      tmp1, guard, write?dereferencet::WRITE:dereferencet::READ);

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
    else
    {
      // We first try the simplifier: this is to support stuff like
      // ((char *)&((type *) 0)->mem - (char *)((type *) 0)))
      // If this fails, we simply dereference.

      exprt tmp_copy=expr;
      simplify(tmp_copy, ns);

      if(tmp_copy.is_constant() ||
         (tmp_copy.id()==ID_typecast &&
          tmp_copy.operands().size()==1 &&
          tmp_copy.op0().is_constant()))
      {
        tmp_copy.location()=expr.location();
        expr=tmp_copy;
      }
      else
        dereference_rec_address_of(object, state, guard);
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
  // needs to be renamed to level 1
  assert(!state.call_stack.empty());
  state.top().level1.rename(expr);

  // start the recursion!
  guardt guard;  
  dereference_rec(expr, state, guard, write);
}
