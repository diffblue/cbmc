/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

#include <hash_cont.h>
#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>
#include <guard.h>
#include <cprover_prefix.h>
#include <prefix.h>

#include <pointer-analysis/value_sets.h>
#include <goto-programs/remove_skip.h>

#include "weak_memory.h"
#include "rw_set.h"

typedef enum { RMO, TSO } modelt;

class shared_bufferst
{
public:
  shared_bufferst(contextt &_context):context(_context)
  {
  }

  class varst
  {
  public:
    // older stuff has the higher index
    irep_idt w_used0, w_used1;
    irep_idt w_buff0, w_buff1;
    
    typet type;
  };
  
  typedef std::map<irep_idt, varst> var_mapt;
  var_mapt var_map;

  const varst &operator()(const irep_idt &object);
  
  void add_aux_code(goto_functionst &goto_functions) const;

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &id_lhs,
    const exprt &rhs) const;

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &id_lhs,
    const irep_idt &id_rhs) const
  {
    namespacet ns(context);
    assignment(goto_program, t, location, id_lhs, symbol_expr(ns.lookup(id_rhs)));
  }
  
  bool track(const irep_idt &id) const
  {
    namespacet ns(context);
    const symbolt &symbol=ns.lookup(id);
    if(symbol.thread_local) return false;
    if(has_prefix(id2string(id), CPROVER_PREFIX))
      return false;
  }

  irep_idt choice(const std::string &suffix)
  {
    return add("weak::choice", suffix, bool_typet());
  }
  
protected:
  contextt &context;

  irep_idt add(
    const irep_idt &object,
    const std::string &suffix,
    const typet &type);

  void add_initialization(goto_programt &goto_program) const;
  
};

/*******************************************************************\

Function: shared_bufferst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const shared_bufferst::varst &shared_bufferst::operator()(const irep_idt &object)
{
  var_mapt::const_iterator it=var_map.find(object);
  if(it!=var_map.end()) return it->second;
  
  varst &vars=var_map[object];
  
  namespacet ns(context);
  const symbolt &symbol=ns.lookup(object);

  vars.type=symbol.type;

  vars.w_used0=add(object, "$w_used0", bool_typet());
  vars.w_used1=add(object, "$w_used1", bool_typet());
  vars.w_buff0=add(object, "$w_buff0", symbol.type);
  vars.w_buff1=add(object, "$w_buff1", symbol.type);
  
  return vars;
}

/*******************************************************************\

Function: shared_bufferst::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt shared_bufferst::add(
  const irep_idt &object,
  const std::string &suffix,
  const typet &type)
{
  const irep_idt identifier=id2string(object)+suffix;

  const contextt::symbolst::const_iterator it=
    context.symbols.find(identifier);

  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.base_name=identifier;
  new_symbol.type=type;
  new_symbol.static_lifetime=true;
  new_symbol.value.make_nil();

  symbolt *symbol_ptr;
  context.move(new_symbol, symbol_ptr);
  return identifier;
}

/*******************************************************************\

Function: shared_bufferst::add_initialization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_bufferst::add_initialization(goto_programt &goto_program) const
{
  goto_programt::targett t=goto_program.instructions.begin();
  const namespacet ns(context);

  for(var_mapt::const_iterator
      it=var_map.begin();
      it!=var_map.end();
      it++)
  {
    locationt location;
    location.make_nil();
    assignment(goto_program, t, location, it->second.w_used0, false_exprt());
    assignment(goto_program, t, location, it->second.w_used1, false_exprt());
  }
}

/*******************************************************************\

Function: shared_bufferst::add_aux_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_bufferst::add_aux_code(goto_functionst &goto_functions) const
{
  // get "main"
  goto_functionst::function_mapt::iterator
    m_it=goto_functions.function_map.find(goto_functions.main_id());

  if(m_it==goto_functions.function_map.end())
    throw "Weak memory instrumentation needs an entry point";

  goto_programt &main=m_it->second.body;
  add_initialization(main);
}

/*******************************************************************\

Function: shared_bufferst::assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_bufferst::assignment(
  goto_programt &goto_program,
  goto_programt::targett &t,
  const locationt &location,
  const irep_idt &id_lhs,
  const exprt &value) const
{
  const namespacet ns(context);

  exprt symbol=symbol_expr(ns.lookup(id_lhs));

  t=goto_program.insert_before(t);
  t->type=ASSIGN;
  t->code=code_assignt(symbol, value);
  t->code.location()=location;
  t->location=location;
  
  t++;
}

/*******************************************************************\

Function: weak_memory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory(
  value_setst &value_sets,
  contextt &context,
  goto_programt &goto_program,
  shared_bufferst &shared_buffers,
  modelt model)
{
  namespacet ns(context);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      rw_set_loct rw_set(ns, value_sets, i_it);
      
      if(rw_set.empty()) continue;
      
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const locationt &location=original_instruction.location;

      // we make the whole thing atomic      
      instruction.make_atomic_begin();
      instruction.location=location;
      i_it++;
      
      // we first perform (non-deterministically) up to 2 writes for
      // stuff that is potentially read
      forall_rw_set_r_entries(e_it, rw_set)
      {
        const shared_bufferst::varst &vars=shared_buffers(e_it->second.object);
        irep_idt choice0=shared_buffers.choice("0");
        irep_idt choice1=shared_buffers.choice("1");
        
        symbol_exprt choice0_expr=symbol_exprt(choice0, bool_typet());
        symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());
      
        symbol_exprt w_buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
        symbol_exprt w_buff1_expr=symbol_exprt(vars.w_buff1, vars.type);
        
        symbol_exprt w_used0_expr=symbol_exprt(vars.w_used0, bool_typet());
        symbol_exprt w_used1_expr=symbol_exprt(vars.w_used1, bool_typet());
        
        exprt nondet_bool_expr=side_effect_expr_nondett(bool_typet());
        
        exprt choice0_rhs=and_exprt(nondet_bool_expr, w_used0_expr);
        exprt choice1_rhs=and_exprt(nondet_bool_expr, w_used1_expr);
        
        // throw 2 Boolean dice
        shared_buffers.assignment(goto_program, i_it, location, choice0, choice0_rhs);
        shared_buffers.assignment(goto_program, i_it, location, choice1, choice1_rhs);
        
        exprt lhs=symbol_exprt(e_it->second.object, vars.type);
        
        exprt value=
          if_exprt(choice0_expr, w_buff0_expr,
            if_exprt(choice1_expr, w_buff1_expr, lhs));

        // write one of the buffer entries
        shared_buffers.assignment(goto_program, i_it, location, e_it->second.object, value);
        
        // update 'used' flags
        exprt w_used0_rhs=if_exprt(choice0_expr, false_exprt(), w_used0_expr);
        exprt w_used1_rhs=and_exprt(if_exprt(choice1_expr, false_exprt(), w_used1_expr), w_used0_expr);

        shared_buffers.assignment(goto_program, i_it, location, vars.w_used0, w_used0_rhs);
        shared_buffers.assignment(goto_program, i_it, location, vars.w_used1, w_used1_rhs);
      }

      // now rotate the write buffers for anything that is written
      forall_rw_set_w_entries(e_it, rw_set)
      {
        const shared_bufferst::varst &vars=shared_buffers(e_it->second.object);
      
        // w_used1=w_used0; w_used0=true;
        shared_buffers.assignment(goto_program, i_it, location, vars.w_used1, vars.w_used0);
        shared_buffers.assignment(goto_program, i_it, location, vars.w_used0, true_exprt());

        // w_buff1=w_buff0; w_buff0=RHS;
        shared_buffers.assignment(goto_program, i_it, location, vars.w_buff1, vars.w_buff0);
        shared_buffers.assignment(goto_program, i_it, location, vars.w_buff0, original_instruction.code.op1());
      }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->location=location;
      i_it++;
        
      i_it--; // the for loop already counts us up
    }
  }
  
  remove_skip(goto_program);  
}

/*******************************************************************\

Function: weak_memory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions,
  modelt model)
{
  shared_bufferst shared_buffers(context);

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=ID_main)
      weak_memory(value_sets, context, f_it->second.body, shared_buffers, model);

  shared_buffers.add_aux_code(goto_functions);
  goto_functions.update();
}

/*******************************************************************\

Function: weak_memory_tso

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory_tso(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions)
{
  weak_memory(value_sets, context, goto_functions, TSO);
}

/*******************************************************************\

Function: weak_memory_rmo

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory_rmo(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions)
{
  weak_memory(value_sets, context, goto_functions, RMO);
}

