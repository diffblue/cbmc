/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#include <expr_util.h>
#include <std_expr.h>
#include <std_code.h>
#include <namespace.h>

#include <langapi/language_util.h>

#include <pointer-analysis/goto_program_dereference.h>

#include "rw_set.h"

/*******************************************************************\

Function: rw_set_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_set_baset::output(std::ostream &out) const
{
  out << "READ:" << std::endl;
  for(entriest::const_iterator it=r_entries.begin();
      it!=r_entries.end();
      it++)
  {
    out << it->second.object << " if "
        << from_expr(ns, "", it->second.guard) << std::endl;
  }
  
  out << std::endl;

  out << "WRITE:" << std::endl;
  for(entriest::const_iterator it=w_entries.begin();
      it!=w_entries.end();
      it++)
  {
    out << it->second.object << " if "
        << from_expr(ns, "", it->second.guard) << std::endl;
  }
}

/*******************************************************************\

Function: rw_set_loct::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_set_loct::compute()
{
  if(target->is_assign())
  {
    assert(target->code.operands().size()==2);
    assign(target->code.op0(), target->code.op1());
  }
  else if(target->is_goto() ||
          target->is_assume() ||
          target->is_assert())
  {
    read(target->guard);
  }
  else if(target->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(target->code);

    read(code_function_call.function());
    
    // do operands
    for(code_function_callt::argumentst::const_iterator
        it=code_function_call.arguments().begin();
        it!=code_function_call.arguments().end();
        it++)
      read(*it);
    
    if(code_function_call.lhs().is_not_nil())
      write(code_function_call.lhs());
  }
}

/*******************************************************************\

Function: rw_set_loct::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_set_loct::assign(const exprt &lhs, const exprt &rhs)
{
  read(rhs);
  read_write_rec(lhs, false, true, "", guardt());
}

/*******************************************************************\

Function: rw_set_loct::read_write_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_set_loct::read_write_rec(
  const exprt &expr,
  bool r, bool w,
  const std::string &suffix,
  const guardt &guard)
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);

    irep_idt object=id2string(symbol_expr.get_identifier())+suffix;

    if(r)
    {
      entryt &entry=r_entries[object];
      entry.object=object;
      entry.symbol_expr=symbol_expr;
      entry.guard=guard.as_expr(); // should 'OR'
    }
    
    if(w)
    {
      entryt &entry=w_entries[object];
      entry.object=object;
      entry.symbol_expr=symbol_expr;
      entry.guard=guard.as_expr(); // should 'OR'
    }
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    const std::string &component_name=expr.get_string(ID_component_name);
    read_write_rec(expr.op0(), r, w, "."+component_name+suffix, guard);
  }
  else if(expr.id()==ID_index)
  {
    // we don't distinguish the array elements for now
    assert(expr.operands().size()==2);
    read_write_rec(expr.op0(), r, w, "[]"+suffix, guard);
    read(expr.op1(), guard);
  }
  else if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);
    read(expr.op0(), guard);

    exprt tmp=expr;
    dereference(target, tmp, ns, value_sets);
    
    read_write_rec(tmp, r, w, suffix, guard);
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    read(expr.op0(), guard);
    
    guardt true_guard(guard);
    true_guard.add(expr.op0());
    read_write_rec(expr.op1(), r, w, suffix, true_guard);
    
    guardt false_guard(guard);
    false_guard.add(gen_not(expr.op0()));
    read_write_rec(expr.op2(), r, w, suffix, false_guard);
  }
  else
  {
    forall_operands(it, expr)
      read_write_rec(*it, r, w, suffix, guard);
  }
}

/*******************************************************************\

Function: rw_set_functiont::compute_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_set_functiont::compute_rec(const exprt &function)
{
  if(function.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(function).get_identifier();

    goto_functionst::function_mapt::const_iterator f_it=
      goto_functions.function_map.find(id);

    if(f_it!=goto_functions.function_map.end())
    {
      const goto_programt &body=f_it->second.body;

      forall_goto_program_instructions(i_it, body)
      {
        *this+=rw_set_loct(ns, value_sets, i_it);
      }
    }
  }
  else if(function.id()==ID_if)
  {
    compute_rec(to_if_expr(function).true_case());
    compute_rec(to_if_expr(function).false_case());
  }
} 
