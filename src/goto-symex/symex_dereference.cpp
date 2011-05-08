/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>

#include <pointer-analysis/dereference.h>
#include <pointer-analysis/rewrite_index.h>
#include <langapi/language_util.h>

#include "goto_symex.h"
#include "renaming_ns.h"
#include "symex_dereference_state.h"

/*******************************************************************\

Function: goto_symext::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::dereference_rec(
  exprt &expr,
  guardt &guard,
  dereferencet &dereference,
  const bool write)
{
  if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference takes one operand";

    exprt tmp1;
    tmp1.swap(expr.op0());

    // first make sure there are no dereferences in there
    dereference_rec(tmp1, guard, dereference, false);
    
    exprt tmp2=dereference.dereference(
      tmp1, guard, write?dereferencet::WRITE:dereferencet::READ);

    expr.swap(tmp2);
  }
  else if(expr.id()=="implicit_dereference")
  {
    // old stuff, should be gone
    assert(false);
  }
  else if(expr.id()==ID_index &&
          expr.operands().size()==2 &&
          expr.op0().type().id()==ID_pointer)
  {
    // old stuff, will go away
  
    exprt tmp=rewrite_index(to_index_expr(expr)).pointer();

    // first make sure there are no dereferences in there
    dereference_rec(tmp, guard, dereference, false);

    dereference.dereference(tmp, guard, write?dereferencet::WRITE:dereferencet::READ);
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
    
      // do rec. call, as p might have dereferencing in it
      dereference_rec(expr, guard, dereference, false);
    }
    else
    {
      // Could be member, could be if, could be index.
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
        dereference_rec(object, guard, dereference, false);
    }
  }
  else
  {
    Forall_operands(it, expr)
      dereference_rec(*it, guard, dereference, write);
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
  symex_dereference_statet symex_dereference_state(*this, state);
  renaming_nst renaming_ns(ns, state);

  dereferencet dereference(
    renaming_ns,
    new_context,
    options,
    symex_dereference_state);
    
  // needs to be renamed to level 1
  assert(!state.call_stack.empty());
  state.top().level1.rename(expr);

  guardt guard;  
  dereference_rec(expr, guard, dereference, write);
}
