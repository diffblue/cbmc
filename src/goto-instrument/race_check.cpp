/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#include <hash_cont.h>
#include <std_expr.h>
#include <expr_util.h>
#include <guard.h>
#include <symbol_table.h>
#include <prefix.h>

#include <pointer-analysis/value_sets.h>
#include <goto-programs/remove_skip.h>

#include "race_check.h"
#include "rw_set.h"

class w_guardst
{
public:
  w_guardst(symbol_tablet &_symbol_table):symbol_table(_symbol_table)
  {
  }
  
  std::list<irep_idt> w_guards;

  const symbolt &get_guard_symbol(const irep_idt &object);
  
  const exprt get_guard_symbol_expr(const irep_idt &object)
  {
    return symbol_expr(get_guard_symbol(object));
  }
  
  const exprt get_w_guard_expr(const rw_set_baset::entryt &entry)
  {
    return get_guard_symbol_expr(entry.object);
  }
  
  const exprt get_assertion(const rw_set_baset::entryt &entry)
  {
    return gen_not(get_guard_symbol_expr(entry.object));
  }
  
  void add_initialization(goto_programt &goto_program) const;
  
protected:
  symbol_tablet &symbol_table;
};

/*******************************************************************\

Function: w_guardst::get_guard_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &w_guardst::get_guard_symbol(const irep_idt &object)
{
  const irep_idt identifier=id2string(object)+"$w_guard";

  const symbol_tablet::symbolst::const_iterator it=
    symbol_table.symbols.find(identifier);

  if(it!=symbol_table.symbols.end())
    return it->second;
    
  w_guards.push_back(identifier);

  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.base_name=identifier;
  new_symbol.type=bool_typet();
  new_symbol.is_static_lifetime=true;
  new_symbol.value.make_false();
  
  symbolt *symbol_ptr;
  symbol_table.move(new_symbol, symbol_ptr);
  return *symbol_ptr;
}

/*******************************************************************\

Function: w_guardst::add_initialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void w_guardst::add_initialization(goto_programt &goto_program) const
{
  goto_programt::targett t=goto_program.instructions.begin();
  const namespacet ns(symbol_table);

  for(std::list<irep_idt>::const_iterator
      it=w_guards.begin();
      it!=w_guards.end();
      it++)
  {
    exprt symbol=symbol_expr(ns.lookup(*it));
  
    t=goto_program.insert_before(t);
    t->type=ASSIGN;
    t->code=code_assignt(symbol, false_exprt());
    
    t++;
  }
}

/*******************************************************************\

Function: comment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string comment(const rw_set_baset::entryt &entry, bool write)
{
  std::string result;
  if(write)
    result="W/W";
  else
    result="R/W";

  result+=" data race on ";
  result+=id2string(entry.object);
  return result;
}

/*******************************************************************\

Function: is_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_shared(
  const namespacet &ns,
  const symbol_exprt &symbol_expr)
{
  const irep_idt &identifier=symbol_expr.get_identifier();

  if(identifier=="c::__CPROVER_alloc" ||
     identifier=="c::__CPROVER_alloc_size" ||
     identifier=="c::stdin" ||
     identifier=="c::stdout" ||
     identifier=="c::stderr" ||
     identifier=="c::sys_nerr" ||
     has_prefix(id2string(identifier), "symex::invalid_object") ||
     has_prefix(id2string(identifier), "symex_dynamic::dynamic_object"))
    return false; // no race check

  const symbolt &symbol=ns.lookup(identifier);
  return symbol.is_shared();
}

/*******************************************************************\

Function: race_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_shared_entries(
  const namespacet &ns,
  const rw_set_baset &rw_set)
{
  for(rw_set_baset::entriest::const_iterator
      it=rw_set.r_entries.begin();
      it!=rw_set.r_entries.end();
      it++)
    if(is_shared(ns, it->second.symbol_expr))
      return true;

  for(rw_set_baset::entriest::const_iterator
      it=rw_set.w_entries.begin();
      it!=rw_set.w_entries.end();
      it++)
    if(is_shared(ns, it->second.symbol_expr))
      return true;

  return false;
}

/*******************************************************************\

Function: race_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void race_check(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  w_guardst &w_guards)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      rw_set_loct rw_set(ns, value_sets, i_it);
      
      if(!has_shared_entries(ns, rw_set))
        continue;
      
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      
      instruction.make_skip();
      i_it++;

      // now add assignments for what is written -- set
      forall_rw_set_w_entries(e_it, rw_set)
      {      
        if(!is_shared(ns, e_it->second.symbol_expr)) continue;
        
        goto_programt::targett t=goto_program.insert_before(i_it);

        t->type=ASSIGN;
        t->code=code_assignt(
          w_guards.get_w_guard_expr(e_it->second),
          e_it->second.guard);

        t->location=original_instruction.location;
        i_it=++t;
      }

      // insert original statement here
      {
        goto_programt::targett t=goto_program.insert_before(i_it);
        *t=original_instruction;
        i_it=++t;
      }

      // now add assignments for what is written -- reset
      forall_rw_set_w_entries(e_it, rw_set)
      {      
        if(!is_shared(ns, e_it->second.symbol_expr)) continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->type=ASSIGN;
        t->code=code_assignt(
          w_guards.get_w_guard_expr(e_it->second),
          false_exprt());

        t->location=original_instruction.location;
        i_it=++t;
      }

      // now add assertions for what is read and written
      forall_rw_set_r_entries(e_it, rw_set)
      {
        if(!is_shared(ns, e_it->second.symbol_expr)) continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->make_assertion(w_guards.get_assertion(e_it->second));
        t->location=original_instruction.location;
        t->location.set_comment(comment(e_it->second, false));
        i_it=++t;
      }

      forall_rw_set_w_entries(e_it, rw_set)
      {
        if(!is_shared(ns, e_it->second.symbol_expr)) continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->make_assertion(w_guards.get_assertion(e_it->second));
        t->location=original_instruction.location;
        t->location.set_comment(comment(e_it->second, true));
        i_it=++t;
      }

      i_it--; // the for loop already counts us up      
    }
  }
  
  remove_skip(goto_program);  
}

/*******************************************************************\

Function: race_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void race_check(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_programt &goto_program)
{
  w_guardst w_guards(symbol_table);

  race_check(value_sets, symbol_table, goto_program, w_guards);

  w_guards.add_initialization(goto_program);
  goto_program.update();
}

/*******************************************************************\

Function: race_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void race_check(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  w_guardst w_guards(symbol_table);

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=ID_main &&
       f_it->first!="c::__CPROVER_initialize")
      race_check(value_sets, symbol_table, f_it->second.body, w_guards);

  // get "main"
  goto_functionst::function_mapt::iterator
    m_it=goto_functions.function_map.find(goto_functions.main_id());

  if(m_it==goto_functions.function_map.end())
    throw "Race check instrumentation needs an entry point";

  goto_programt &main=m_it->second.body;
  w_guards.add_initialization(main);
  goto_functions.update();
}
