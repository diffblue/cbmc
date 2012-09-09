/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>

#include "basic_symex.h"
#include "goto_symex_state.h"

/*******************************************************************\

Function: basic_symext::symex_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign(
  statet &state,
  const code_assignt &code)
{
  exprt lhs=code.lhs();
  exprt rhs=code.rhs();

  read(lhs);
  read(rhs);
  
  replace_nondet(lhs);
  replace_nondet(rhs);
  
  if(rhs.id()==ID_sideeffect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();
    
    if(statement==ID_function_call)
    {
      assert(side_effect_expr.operands().size()!=0);
    
      if(side_effect_expr.op0().id()!=ID_symbol)
        throw "symex_assign: expected symbol as function";

      const irep_idt &identifier=
        to_symbol_expr(side_effect_expr.op0()).get_identifier();
      
      throw "symex_assign: unexpected function call: "+id2string(identifier);
    }
    else if(statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
      symex_cpp_new(state, lhs, side_effect_expr);
    else if(statement==ID_malloc)
      symex_malloc(state, lhs, side_effect_expr);
    else if(statement==ID_printf)
      symex_printf(state, lhs, side_effect_expr);
    else if(statement==ID_gcc_builtin_va_arg_next)
      symex_gcc_builtin_va_arg_next(state, lhs, side_effect_expr);
    else
      throw "symex_assign: unexpected side effect: "+id2string(statement);
  }
  else
  {
    guardt guard; // NOT the state guard!
    symex_assign_rec(state, lhs, nil_exprt(), rhs, guard, VISIBLE);
  }
}

/*******************************************************************\

Function: basic_symext::add_to_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt basic_symext::add_to_lhs(
  const exprt &lhs,
  const exprt &what)
{
  assert(lhs.id()!=ID_symbol);
  exprt tmp_what=what;

  if(tmp_what.id()!=ID_symbol)
  {
    assert(tmp_what.operands().size()>=1);
    tmp_what.op0().make_nil();
  }

  exprt new_lhs=lhs;

  exprt *p=&new_lhs;

  while(p->is_not_nil())
  {
    assert(p->id()!=ID_symbol);
    assert(p->operands().size()>=1);
    p=&p->op0();
  }

  *p=tmp_what;
  return new_lhs;
}

/*******************************************************************\

Function: basic_symext::symex_assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_rec(
  statet &state,
  const exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  if(lhs.id()==ID_symbol)
    symex_assign_symbol(state, to_symbol_expr(lhs), full_lhs, rhs, guard, visibility);
  else if(lhs.id()==ID_index)
    symex_assign_array(state, to_index_expr(lhs), full_lhs, rhs, guard, visibility);
  else if(lhs.id()==ID_member)
    symex_assign_member(state, to_member_expr(lhs), full_lhs, rhs, guard, visibility);
  else if(lhs.id()==ID_if)
    symex_assign_if(state, to_if_expr(lhs), full_lhs, rhs, guard, visibility);
  else if(lhs.id()==ID_typecast)
    symex_assign_typecast(state, to_typecast_expr(lhs), full_lhs, rhs, guard, visibility);
  else if(lhs.id()==ID_string_constant ||
          lhs.id()=="NULL-object" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
    symex_assign_byte_extract(state, lhs, full_lhs, rhs, guard, visibility);
  else
    throw "assignment to `"+lhs.id_string()+"' not handled";
}

/*******************************************************************\

Function: basic_symext::symex_assign_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_symbol(
  statet &state,
  const symbol_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  exprt ssa_rhs=rhs;
  
  // put assignment guard into the rhs
  if(!guard.empty())
  {
    if_exprt tmp_ssa_rhs;
    tmp_ssa_rhs.type()=ssa_rhs.type();
    tmp_ssa_rhs.cond()=guard.as_expr();
    tmp_ssa_rhs.true_case()=ssa_rhs;
    tmp_ssa_rhs.false_case()=lhs;
    tmp_ssa_rhs.swap(ssa_rhs);
  }
  
  symbol_exprt original_lhs=lhs;
  state.get_original_name(original_lhs);
  
  state.rename(ssa_rhs, ns);
  do_simplify(ssa_rhs);

  exprt ssa_full_lhs=full_lhs;
  state.rename(ssa_full_lhs, ns);
  
  symbol_exprt ssa_lhs=lhs;
  state.rename(ssa_lhs, ns, goto_symex_statet::L1);
  state.assignment(ssa_lhs, ssa_rhs, ns, constant_propagation);
  
  ssa_full_lhs=add_to_lhs(ssa_full_lhs, ssa_lhs);

  guardt tmp_guard(state.guard);
  tmp_guard.append(guard);
  
  // do the assignment
  target.assignment(
    tmp_guard,
    ssa_lhs, original_lhs,
    ssa_full_lhs, add_to_lhs(full_lhs, original_lhs),
    ssa_rhs, 
    state.source,
    symex_targett::STATE);
}

/*******************************************************************\

Function: basic_symext::symex_assign_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_typecast(
  statet &state,
  const typecast_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  // these may come from dereferencing on the lhs
  
  assert(lhs.operands().size()==1);
  
  exprt rhs_typecasted=rhs;
  rhs_typecasted.make_typecast(lhs.op0().type());
  
  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);
  
  symex_assign_rec(
    state, lhs.op0(), new_full_lhs, rhs_typecasted, guard, visibility);
}

/*******************************************************************\

Function: basic_symext::symex_assign_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_array(
  statet &state,
  const index_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  // lhs must be index operand
  // that takes two operands: the first must be an array
  // the second is the index

  if(lhs.operands().size()!=2)
    throw "index must have two operands";

  const exprt &lhs_array=lhs.array();
  const exprt &lhs_index=lhs.index();
  const typet &lhs_type=ns.follow(lhs_array.type());

  if(lhs_type.id()!=ID_array)
    throw "index must take array type operand, but got `"+
          lhs_type.id_string()+"'";

  // turn
  //   a[i]=e
  // into
  //   a'==a WITH [i:=e]

  exprt new_rhs(ID_with, lhs_type);
  new_rhs.copy_to_operands(lhs_array, lhs_index, rhs);
  
  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs_array, new_full_lhs, new_rhs, guard, visibility);
}

/*******************************************************************\

Function: basic_symext::symex_assign_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_member(
  statet &state,
  const member_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  // symbolic execution of a struct member assignment

  // lhs must be member operand
  // that takes one operands, which must be a structure

  exprt lhs_struct=lhs.op0();
  typet struct_type=ns.follow(lhs_struct.type());

  if(struct_type.id()!=ID_struct &&
     struct_type.id()!=ID_union)
    throw "member must take struct/union type operand but got "
          +struct_type.pretty();

  const irep_idt &component_name=lhs.get(ID_component_name);

  // typecasts involved? C++ does that for inheritance.
  if(lhs_struct.id()==ID_typecast)
  {
    assert(lhs_struct.operands().size()==1);
    
    if(lhs_struct.op0().id()=="NULL-object")
    {
      // ignore, and give up
      return;
    }
    else
    {
      // remove the type cast, we assume that the member is there
      exprt tmp=lhs_struct.op0();
      struct_type=ns.follow(tmp.type());

      if(struct_type.id()==ID_struct ||
         struct_type.id()==ID_union)
        lhs_struct=tmp;
      else
        return; // ignore and give up
    }
  }

  // turn
  //   a.c=e
  // into
  //   a'==a WITH [c:=e]

  exprt new_rhs(ID_with, struct_type);
  new_rhs.copy_to_operands(lhs_struct, exprt(ID_member_name), rhs);
  new_rhs.op1().set(ID_component_name, component_name);
  
  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs_struct, new_full_lhs, new_rhs, guard, visibility);
}

/*******************************************************************\

Function: basic_symext::symex_assign_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_if(
  statet &state,
  const if_exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  // we have (c?a:b)=e;

  unsigned old_guard_size=guard.size();
  
  exprt renamed_guard=lhs.cond();
  state.rename(renamed_guard, ns);
  do_simplify(renamed_guard);

  if(!renamed_guard.is_false())  
  {
    guard.add(renamed_guard);
    symex_assign_rec(state, lhs.true_case(), full_lhs, rhs, guard, visibility);
    guard.resize(old_guard_size);
  }
   
  if(!renamed_guard.is_true())
  { 
    guard.add(gen_not(renamed_guard));
    symex_assign_rec(state, lhs.false_case(), full_lhs, rhs, guard, visibility);
    guard.resize(old_guard_size);
  }
}

/*******************************************************************\

Function: basic_symext::symex_assign_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_assign_byte_extract(
  statet &state,
  const exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  guardt &guard,
  visibilityt visibility)
{
  // we have byte_extract_X(l, b)=r
  // turn into l=byte_update_X(l, b, r)

  if(lhs.operands().size()!=2)
    throw "byte_extract must have two operands";

  exprt new_rhs;

  if(lhs.id()==ID_byte_extract_little_endian)
    new_rhs.id(ID_byte_update_little_endian);
  else if(lhs.id()==ID_byte_extract_big_endian)
    new_rhs.id(ID_byte_update_big_endian);
  else
    assert(false);

  new_rhs.copy_to_operands(lhs.op0(), lhs.op1(), rhs);
  new_rhs.type()=lhs.op0().type();
  
  exprt new_full_lhs=add_to_lhs(full_lhs, lhs);

  symex_assign_rec(
    state, lhs.op0(), new_full_lhs, new_rhs, guard, visibility);
}

