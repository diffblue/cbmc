/*******************************************************************\

Module: Weakest Preconditions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#include <langapi/language_util.h>

#include <std_expr.h>
#include <std_code.h>
#include <base_type.h>
#include <i2string.h>

#include "wp.h"

/*******************************************************************\

Function: has_nondet

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool has_nondet(const exprt &dest)
{
  forall_operands(it, dest)
    if(has_nondet(*it))
      return true;

  if(dest.id()==ID_sideeffect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(dest);
    const irep_idt &statement=side_effect_expr.get_statement();
    
    if(statement==ID_nondet)
      return true;
  }
  
  return false;
}

/*******************************************************************\

Function: approximate_nondet_rec

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void approximate_nondet_rec(exprt &dest, unsigned &count)
{
  if(dest.id()==ID_sideeffect &&
     to_side_effect_expr(dest).get_statement()==ID_nondet)
  {
    count++;
    dest.set(ID_identifier, "wp::nondet::"+i2string(count));
    dest.id(ID_nondet_symbol);
    return;
  }
  
  Forall_operands(it, dest)
    approximate_nondet_rec(*it, count);
}

/*******************************************************************\

Function: approximate_nondet

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void approximate_nondet(exprt &dest)
{
  static unsigned count=0; // not proper, should be quantified
  approximate_nondet_rec(dest, count);
}

/*******************************************************************\

Function: aliasing

  Inputs:

 Outputs:

 Purpose: consider possible aliasing

\*******************************************************************/

typedef enum { A_MAY, A_MUST, A_MUSTNOT } aliasingt;

aliasingt aliasing(
  const exprt &e1, const exprt &e2,
  const namespacet &ns)
{
  // deal with some dereferencing
  if(e1.id()==ID_dereference &&
     e1.operands().size()==1 &&
     e1.op0().id()==ID_address_of &&
     e1.op0().operands().size()==1)
    return aliasing(e1.op0().op0(), e2, ns);
    
  if(e2.id()==ID_dereference &&
     e2.operands().size()==1 &&
     e2.op0().id()==ID_address_of &&
     e2.op0().operands().size()==1)
    return aliasing(e1, e2.op0().op0(), ns);

  // fairly radical. Ignores struct prefixes and the like.
  if(!base_type_eq(e1.type(), e2.type(), ns))
    return A_MUSTNOT;
    
  // syntactically the same?
  if(e1==e2)
    return A_MUST;

  // the trivial case first
  if(e1.id()==ID_symbol && e2.id()==ID_symbol)
  {
    if(to_symbol_expr(e1).get_identifier()==
       to_symbol_expr(e2).get_identifier())
      return A_MUST;
    else
      return A_MUSTNOT;
  }
    
  // an array or struct will never alias with a variable,
  // nor will a struct alias with an array
  
  if(e1.id()==ID_index || e1.id()==ID_struct)
    if(e1.id()!=e2.id())
      return A_MUSTNOT;

  if(e2.id()==ID_index || e2.id()==ID_struct)
    if(e1.id()!=e2.id())
      return A_MUSTNOT;

  // we give up, and say it may
  // (could do much more here)

  return A_MAY;    
}

/*******************************************************************\

Function: substitute_rec

  Inputs:

 Outputs:

 Purpose: replace 'what' by 'by' in 'dest',
          considering possible aliasing

\*******************************************************************/

void substitute_rec(
  exprt &dest,
  const exprt &what,
  const exprt &by,
  const namespacet &ns)
{
  if(dest.id()!=ID_address_of)
    Forall_operands(it, dest)
      substitute_rec(*it, what, by, ns);

  // possibly substitute?
  if(dest.id()==ID_member ||
     dest.id()==ID_index ||
     dest.id()==ID_dereference ||
     dest.id()==ID_symbol)
  {
    // could these be possible the same?
    switch(aliasing(dest, what, ns))
    {
    case A_MUST:
      dest=by; // they are always the same
      break;

    case A_MAY:
      {
        // consider possible aliasing between 'what' and 'dest'
        exprt what_address=address_of_exprt(what);
        exprt dest_address=address_of_exprt(dest);

        equal_exprt alias_cond=equal_exprt(what_address, dest_address);
        
        if_exprt if_expr;

        if_expr.cond()=alias_cond;
        if_expr.type()=dest.type();
        if_expr.true_case()=by;
        if_expr.false_case()=dest;

        dest=if_expr;
        return;
      }
    
    case A_MUSTNOT:
      // nothing to do
      break;      
    }
  }
}

/*******************************************************************\

Function: rewrite_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rewrite_assignment(exprt &lhs, exprt &rhs)
{
  if(lhs.id()==ID_member) // turn s.x:=e into s:=(s with .x=e)
  {
    const member_exprt member_expr=to_member_expr(lhs);
    irep_idt component_name=member_expr.get_component_name();
    exprt new_lhs=member_expr.struct_op();

    with_exprt new_rhs;
    new_rhs.type()=new_lhs.type();
    new_rhs.old()=new_lhs;
    new_rhs.where().id(ID_member_name);
    new_rhs.where().set(ID_component_name, component_name);
    new_rhs.new_value()=rhs;
    
    lhs=new_lhs;
    rhs=new_rhs;
    
    rewrite_assignment(lhs, rhs); // rec. call
  }
  else if(lhs.id()==ID_index) // turn s[i]:=e into s:=(s with [i]=e)
  {
    const index_exprt index_expr=to_index_expr(lhs);
    exprt new_lhs=index_expr.array();

    with_exprt new_rhs;
    new_rhs.type()=new_lhs.type();
    new_rhs.old()=new_lhs;
    new_rhs.where()=index_expr.index();
    new_rhs.new_value()=rhs;
    
    lhs=new_lhs;
    rhs=new_rhs;
    
    rewrite_assignment(lhs, rhs); // rec. call
  }
}

/*******************************************************************\

Function: wp_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wp_assign(
  const code_assignt &code,
  const exprt &post,
  const namespacet &ns)
{
  exprt pre=post;
  
  exprt lhs=code.lhs(),
        rhs=code.rhs();
        
  rewrite_assignment(lhs, rhs);

  // replace lhs by rhs in pre
  substitute_rec(pre, lhs, rhs, ns);
  
  // take care of non-determinism in the RHS
  approximate_nondet(pre);

  return pre;
}

/*******************************************************************\

Function: wp_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wp_assume(
  const code_assumet &code,
  const exprt &post,
  const namespacet &ns)
{
  return implies_exprt(code.assumption(), post);
}

/*******************************************************************\

Function: wp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wp(
  const codet &code,
  const exprt &post,
  const namespacet &ns)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_assign)
    return wp_assign(to_code_assign(code), post, ns);
  else if(statement==ID_assume)
    return wp_assume(to_code_assume(code), post, ns);
  else if(statement==ID_skip)
    return post;
  else if(statement==ID_decl)
    return post; // ignored
  else if(statement==ID_assert)
    return post;   
  else if(statement==ID_expression)
    return post;
  else if(statement==ID_printf)
    return post; // ignored
  else if(statement==ID_free)
    return post; // ignored
  else if(statement==ID_asm)
    return post; // ignored
  else
    throw "sorry, wp("+id2string(statement)+"...) not implemented";
}
