/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#include <expr_util.h>
#include <std_expr.h>
#include <namespace.h>

#include <pointer-analysis/goto_program_dereference.h>

#include "rw_set.h"

/*******************************************************************\

Function: rw_sett::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_sett::compute(const codet &code)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_assign)
  {
    assert(code.operands().size()==2);
    assign(code.op0(), code.op1());
  }
}

/*******************************************************************\

Function: rw_sett::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_sett::assign(const exprt &lhs, const exprt &rhs)
{
  read(rhs);
  read_write_rec(lhs, false, true, "", guardt());
}

/*******************************************************************\

Function: rw_sett::read_write_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_sett::read_write_rec(
  const exprt &expr,
  bool r, bool w,
  const std::string &suffix,
  const guardt &guard)
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);

    const symbolt *symbol;
    if(!ns.lookup(symbol_expr.get_identifier(), symbol))
    {
      if(!symbol->static_lifetime)
        return; // ignore for now
        
      if(symbol->thread_local)
        return; // must ignore
        
      if(symbol->name=="c::__CPROVER_alloc" ||
         symbol->name=="c::__CPROVER_alloc_size" ||
         symbol->name=="c::stdin" ||
         symbol->name=="c::stdout" ||
         symbol->name=="c::stderr" ||
         symbol->name=="c::sys_nerr")
        return; // ignore for now
    }
    
    irep_idt object=id2string(symbol_expr.get_identifier())+suffix;
    
    entryt &entry=entries[object];
    entry.object=object;
    entry.r=entry.r || r;
    entry.w=entry.w || w;
    entry.guard=guard.as_expr();
  }
  else if(expr.id()=="member")
  {
    assert(expr.operands().size()==1);
    const std::string &component_name=expr.get_string("component_name");
    read_write_rec(expr.op0(), r, w, "."+component_name+suffix, guard);
  }
  else if(expr.id()=="index")
  {
    // we don't distinguish the array elements for now
    assert(expr.operands().size()==2);
    read_write_rec(expr.op0(), r, w, "[]"+suffix, guard);
    read(expr.op1(), guard);
  }
  else if(expr.id()=="dereference")
  {
    assert(expr.operands().size()==1);
    read(expr.op0(), guard);

    exprt tmp(expr.op0());
    dereference(target, tmp, ns, value_sets);

    read_write_rec(tmp, r, w, suffix, guard);
  }
  else if(expr.id()=="address_of" ||
          expr.id()=="implicit_address_of")
  {
    assert(expr.operands().size()==1);
    
  }
  else if(expr.id()=="if")
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
