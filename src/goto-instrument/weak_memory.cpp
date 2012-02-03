/*******************************************************************\

Module: Weak Memory Instrumentation for Threaded Goto Programs

Author: Daniel Kroening, Vincent Nimal

Date: September 2011

\*******************************************************************/

#include <sstream>

#include <hash_cont.h>
#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>
#include <guard.h>
#include <cprover_prefix.h>
#include <prefix.h>
#include <i2string.h>
#include <context.h>

#include <config.h>

#include <pointer-analysis/value_sets.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <goto-programs/remove_skip.h>

#include <goto-programs/goto_convert_class.h>
#include <ansi-c/literals/convert_string_literal.h>

#if 0
#include <natural-loops/control_flow_graph.h>
#include <natural-loops/loops.h>
#endif

#include "weak_memory.h"
#include "rw_set.h"

#if 0
#include "cycle_detection.h"
#endif

#if 0
class shared_bufferst
{
public:
  shared_bufferst(contextt &_context, unsigned _nb_threads):
    context(_context),
    nb_threads(_nb_threads+1),
    uniq(0)
  {
  }

  class varst
  {
  public:
    // Older stuff has the higher index.
    // Shared buffer.
    irep_idt w_buff0, w_buff1;

    // Are those places empty?
    irep_idt w_buff0_used, w_buff1_used;

    // Delays write buffer flush: just to make some swaps between mem and buff 
    // -- this is to model lhs := rhs with rhs reading in the buffer without 
    // affecting the memory (Note: we model lhs := rhs by rhs := ..., then lhs := rhs)
    irep_idt mem_tmp;
    irep_idt flush_delayed;

    // Thread: Was it me who wrote at this place?
    std::vector<irep_idt> r_buff0_thds, r_buff1_thds;
   
    // for delayed read:
    irep_idt read_delayed;
    irep_idt read_delayed_var;
    //irep_idt read_new_var;
 
    typet type;
  };
  
  typedef std::map<irep_idt, varst> var_mapt;
  var_mapt var_map;

  // instructions in violation cycles (to be instrumented)
  std::set<irep_idt> cycles; // variables in the cycles
  std::multimap<irep_idt,locationt> cycles_loc; // events instrumented: var->locations in the code
  std::multimap<irep_idt,locationt> cycles_r_loc; // events in cycles: var->locations

  const varst &operator()(const irep_idt &object);
  
  void add_initialization_code(goto_functionst &goto_functions);

  void delay_read(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &read_object,
    const irep_idt &write_object
  );

  void flush_read(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &write_object
  );

  void write(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &object,
    goto_programt::instructiont &original_instruction,
    const unsigned current_thread);

  void det_flush(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &object,
    const unsigned current_thread);

  void nondet_flush(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &object,
    const unsigned current_thread,
    const bool tso_pso_rmo);

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &id_lhs,
    const exprt &rhs);

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const locationt &location,
    const irep_idt &id_lhs,
    const irep_idt &id_rhs)
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

  bool is_buffered(
    const namespacet&, 
    const symbol_exprt&, 
    bool is_write);
 
  bool is_buffered_in_general(
    const namespacet&, 
    const symbol_exprt&, 
    bool is_write);

  void weak_memory(
    value_setst &value_sets,
    contextt &context,
    goto_programt &goto_program,
    weak_memory_modelt model,
    goto_functionst &goto_functions
  );

  void affected_by_delay(
    class contextt &context,
    value_setst &value_sets,
    goto_functionst &goto_functions);
 
protected:
  contextt &context;
  
  // number of threads interferring
  unsigned nb_threads;

  // instrumentations (not to be instrumented again)
  std::set<irep_idt> instrumentations;

  // variables (non necessarily shared) affected by reads delay
public:
  std::set<irep_idt> affected_by_delay_set;

protected:
  // for fresh variables
  unsigned uniq;

  std::string unique();

  irep_idt add(
    const irep_idt &object,
    const std::string &suffix,
    const typet &type);

  irep_idt add_fresh_var(
    const irep_idt &object,
    const std::string &suffix,
    const typet &type);


  void add_initialization(goto_programt &goto_program);
};

/*******************************************************************\

Function: int2str

  Inputs:
 
 Outputs:

 Purpose:

\*******************************************************************/

const std::string int2str(const int n)
{
  std::ostringstream s;
  s<<n;
  return s.str();
}

std::string shared_bufferst::unique (void)
{
  std::cout<<"$fresh#"+int2str(uniq)<<std::endl;
  return "$fresh#"+int2str(uniq++);
}

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

  vars.w_buff0=add(object, "$w_buff0", symbol.type);
  vars.w_buff1=add(object, "$w_buff1", symbol.type);

  vars.w_buff0_used=add(object, "$w_buff0_used", bool_typet());
  vars.w_buff1_used=add(object, "$w_buff1_used", bool_typet());

  vars.mem_tmp=add(object, "$mem_tmp", symbol.type);
  vars.flush_delayed=add(object, "$flush_delayed", bool_typet());

  vars.read_delayed=add(object, "$read_delayed", bool_typet());
  vars.read_delayed_var=add(object, "$read_delayed_var", pointer_typet(symbol.type));
//  vars.read_new_var=add(object, "$read_new_var", symbol.type);

  unsigned cnt;
  for(cnt=0;cnt<nb_threads;cnt++)
  {
    vars.r_buff0_thds.push_back(
      shared_bufferst::add(
        object, 
        "$r_buff0_thd"+int2str(cnt), bool_typet()));
    vars.r_buff1_thds.push_back(
      shared_bufferst::add(
        object, "$r_buff1_thd"+int2str(cnt), 
        bool_typet()));
  }

  return vars;
}

/*******************************************************************\

Function: shared_bufferst::add

  Inputs: var, suffix, type of the var

 Outputs: identifier of the new var

 Purpose: add a new var for instrumenting the input var

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

  instrumentations.insert(identifier);

  symbolt *symbol_ptr;
  context.move(new_symbol, symbol_ptr);
  return identifier;
}

irep_idt shared_bufferst::add_fresh_var(
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

void shared_bufferst::add_initialization(goto_programt &goto_program)
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

    assignment(goto_program, t, location, it->second.w_buff0_used, false_exprt());
    assignment(goto_program, t, location, it->second.w_buff1_used, false_exprt());
    assignment(goto_program, t, location, it->second.flush_delayed, false_exprt());
    assignment(goto_program, t, location, it->second.read_delayed, false_exprt());
    assignment(goto_program, t, location, it->second.read_delayed_var, null_pointer_exprt(pointer_typet(it->second.type)));
 
    for(
      std::vector<irep_idt>::const_iterator l_it=
        it->second.r_buff0_thds.begin();
      l_it!=it->second.r_buff0_thds.end();
      l_it++
    )
      assignment(goto_program, t, location, *l_it, false_exprt());

    for(
      std::vector<irep_idt>::const_iterator l_it=
        it->second.r_buff1_thds.begin();
      l_it!=it->second.r_buff1_thds.end();
      l_it++
    )
      assignment(goto_program, t, location, *l_it, false_exprt());
  }
}

/*******************************************************************\

Function: shared_bufferst::add_initialization_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_bufferst::add_initialization_code(goto_functionst &goto_functions)
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

 Purpose: add an assignment in the goto-program

\*******************************************************************/

void shared_bufferst::assignment(
  goto_programt &goto_program,
  goto_programt::targett &t,
  const locationt &location,
  const irep_idt &id_lhs,
  const exprt &value)
{
  const namespacet ns(context);

  exprt symbol=symbol_expr(ns.lookup(id_lhs));

  t=goto_program.insert_before(t);
  t->type=ASSIGN;
  t->code=code_assignt(symbol, value);
  t->code.location()=location;
  t->location=location;
 
  //instrumentations.insert((const irep_idt) (t->code.id()));
 
  t++;
}

/*******************************************************************\

Function: shared_bufferst::delay_read

  Inputs:

 Outputs:

 Purpose: delays a read (Power)

\*******************************************************************/

void shared_bufferst::delay_read(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const locationt &location,
  const irep_idt &read_object,
  const irep_idt &write_object)
{
/* option 1 */
/*
  assignment(goto_program, target, location, vars.read_delayed, true_exprt());
  assignment(goto_program, target, location, vars.read_delayed_var, read_object);

  const irep_idt& new_var=add_fresh_var(write_object,unique(),vars.type);

  assignment(goto_program, target, location, vars.read_new_var, new_var);

  // initial write, but from the new variable now
  assignment(goto_program, target, location, write_object, new_var);*/

/* option 2 */
  const varst &vars=(*this)(write_object);

  const symbol_exprt read_object_expr = symbol_exprt(read_object, vars.type);

  assignment(goto_program, target, location, vars.read_delayed, true_exprt());
  assignment(goto_program, target, location, vars.read_delayed_var, address_of_exprt( read_object_expr ));
}

/*******************************************************************\

Function: shared_bufferst::flush_read

  Inputs:

 Outputs:

Purpose: flushes read (Power)
 
\*******************************************************************/

void shared_bufferst::flush_read(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const locationt &location,
  const irep_idt &write_object)
{
/* option 1 */
/*  const varst &vars=(*this)(write_object);

  const symbol_exprt fresh_var_expr=symbol_exprt(vars.read_new_var, vars.type);
  const symbol_exprt var_expr=symbol_exprt(vars.read_delayed_var, vars.type);
  const exprt eq_expr=equal_exprt(var_expr, fresh_var_expr);

  const symbol_exprt cond_delayed_expr=symbol_exprt(vars.read_delayed, bool_typet());
  const exprt if_expr=if_exprt(cond_delayed_expr, eq_expr, true_exprt());

  target=goto_program.insert_before(target);
  target->type=ASSUME;
  target->guard=if_expr;
  target->guard.location()=location;
  target->location=location;

  target++;

  assignment(goto_program, target, location, vars.read_delayed, false_exprt());*/
}

/*******************************************************************\

Function: shared_bufferst::write

  Inputs:

 Outputs:

 Purpose: instruments write

\*******************************************************************/

void shared_bufferst::write(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const locationt &location,
  const irep_idt &object,
  goto_programt::instructiont &original_instruction,
  const unsigned current_thread)
{
  const varst &vars=(*this)(object);

  // We rotate the write buffers for anything that is written.
  assignment(goto_program, target, location, vars.w_buff1, vars.w_buff0);
  assignment(
    goto_program, target, location, vars.w_buff0, 
    original_instruction.code.op1());

  // We update the used flags
  assignment(goto_program, target, location, vars.w_buff1_used, vars.w_buff0_used);
  assignment(goto_program, target, location, vars.w_buff0_used, true_exprt());

  // We should not exceed the buffer size -- inserts assertion for dynamically checking this
  const exprt buff0_used_expr=symbol_exprt(vars.w_buff0_used, bool_typet());
  const exprt buff1_used_expr=symbol_exprt(vars.w_buff1_used, bool_typet());
  const exprt cond_expr=not_exprt( and_exprt(buff1_used_expr,buff0_used_expr) );

  target=goto_program.insert_before(target);
  target->guard=cond_expr;
  target->type=ASSERT;
  target->code=code_assertt();
  target->code.location()=location;
  target->location=location;
  target++;

  // We update writers ownership of the values in the buffer
  for(unsigned cnt=0; cnt<nb_threads; cnt++)
    assignment(goto_program, target, location, vars.r_buff1_thds[cnt], vars.r_buff0_thds[cnt]);

  // We update the lucky new author of this value in the buffer
  assignment(goto_program, target, location, vars.r_buff0_thds[current_thread], true_exprt());
}

/*******************************************************************\

Function: shared_bufferst::det_flush

  Inputs:

 Outputs:

 Purpose: flush buffers (instruments fence)

\*******************************************************************/

void shared_bufferst::det_flush(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const locationt &location,
  const irep_idt &object,
  const unsigned current_thread)
{
  // mostly for instrumenting the fences. A thread only flushes the values it wrote in the buffer.
  const varst &vars=(*this)(object);

  // current value in the memory
  const exprt lhs=symbol_exprt(object, vars.type);

  // if buff0 from this thread, uses it to update the memory (the most recent value, or last write 
  // by -ws-> ); if not, if buff1 from this thread, uses it; if not, keeps the current memory value
  const exprt buff0_expr = symbol_exprt(vars.w_buff0, vars.type);
  const exprt buff1_expr = symbol_exprt(vars.w_buff1, vars.type);

  const exprt buff0_used_expr = symbol_exprt(vars.w_buff0_used, bool_typet());
  const exprt buff1_used_expr = symbol_exprt(vars.w_buff1_used, bool_typet());

  const exprt buff0_mine_expr = symbol_exprt(vars.r_buff0_thds[current_thread], bool_typet());
  const exprt buff1_mine_expr = symbol_exprt(vars.r_buff1_thds[current_thread], bool_typet());

  const exprt buff0_used_and_mine_expr = and_exprt(buff0_used_expr, buff0_mine_expr);
  const exprt buff1_used_and_mine_expr = and_exprt(buff1_used_expr, buff1_mine_expr);

  const exprt new_value_expr = if_exprt(
    buff0_used_and_mine_expr,
    buff0_expr,
    if_exprt(
      buff1_used_and_mine_expr,
      buff1_expr,
      lhs
    )
  );
    
  // We update (or not) the value in the memory
  assignment(goto_program, target, location, object, new_value_expr);

  // We udpate the flags of the buffer
  // if buff0 used and mine, then it is no more used, as we flushed the last write and -ws->
  // imposes not to have other writes in the buffer
  assignment(goto_program, target, location, vars.w_buff0_used,
    if_exprt(
      buff0_used_and_mine_expr,
      false_exprt(),
      buff0_used_expr
    )
  );

  // buff1 used and mine & not buff0 used and mine, then it no more used
  // if buff0 is used and mine, then, by ws, buff1 is no more used
  // otherwise, remains as it is
  const exprt buff0_or_buff1_used_and_mine_expr = or_exprt(
    buff0_used_and_mine_expr,
    buff1_used_and_mine_expr    
  );

  assignment(goto_program, target, location, vars.w_buff1_used,
    if_exprt(
      buff0_or_buff1_used_and_mine_expr,
      false_exprt(),
      buff1_used_expr
    )
  );  

  // We update the ownerships
  // if buff0 mine and used, flushed, so belongs to nobody
  const exprt buff0_thd_expr = symbol_exprt(vars.r_buff0_thds[current_thread], bool_typet());

  assignment(goto_program, target, location, vars.r_buff0_thds[current_thread], 
    if_exprt(
      buff0_used_and_mine_expr,
      false_exprt(),
      buff0_thd_expr
    )
  );

  // if buff1 used and mine, or if buff0 used and mine, then buff1 flushed and 
  // doesn't belong to anybody
  const exprt buff1_thd_expr = symbol_exprt(vars.r_buff1_thds[current_thread], bool_typet());

  assignment(goto_program, target, location, vars.r_buff1_thds[current_thread],
    if_exprt(
      buff0_or_buff1_used_and_mine_expr,
      false_exprt(),
      buff1_thd_expr
    )
  );
}         

/*******************************************************************\

Function: shared_bufferst::nondet_flush

  Inputs:

 Outputs:

 Purpose: instruments read

\*******************************************************************/

void shared_bufferst::nondet_flush(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const locationt &location,
  const irep_idt &object,
  const unsigned current_thread,
  const bool tso_pso_rmo) // true: tso/pso/rmo; false: power
{
  const varst &vars=(*this)(object);

  // Non deterministic choice
  irep_idt choice0=choice("0");
  irep_idt choice2=choice("2"); //delays the write flush

  const symbol_exprt choice0_expr=symbol_exprt(choice0, bool_typet());  
  const symbol_exprt delay_expr=symbol_exprt(choice2, bool_typet());
  const exprt nondet_bool_expr=side_effect_expr_nondett(bool_typet());

  // throw Boolean dice
  assignment(goto_program, target, location, choice0, nondet_bool_expr);
  assignment(goto_program, target, location, choice2, nondet_bool_expr);

  // Buffers and memory
  const symbol_exprt buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
  const symbol_exprt buff1_expr=symbol_exprt(vars.w_buff1, vars.type);
  const exprt lhs=symbol_exprt(object, vars.type);

  // Buffer uses
  const symbol_exprt buff0_used_expr=symbol_exprt(vars.w_buff0_used, bool_typet());
  const symbol_exprt buff1_used_expr=symbol_exprt(vars.w_buff1_used, bool_typet());

  // Buffer ownerships
  const symbol_exprt buff0_thd_expr=symbol_exprt(vars.r_buff0_thds[current_thread], bool_typet());
  const symbol_exprt buff1_thd_expr=symbol_exprt(vars.r_buff1_thds[current_thread], bool_typet());


  // Will the write be directly flushed, or is it just a read?
  assignment(goto_program, target, location, vars.flush_delayed, delay_expr);
  assignment(goto_program, target, location, vars.mem_tmp, lhs);

  // for Power, only instrumented reads can read from the buffers of other threads
  bool instrumented=false;

  if(!tso_pso_rmo)
    if(cycles.find(object)!=cycles.end())
    {
      typedef std::multimap<irep_idt,locationt>::iterator m_itt;
      std::pair<m_itt,m_itt> ran=cycles_loc.equal_range(object);
      for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
        if(ran_it->second==location)
        {
          instrumented=true;
          break;
        }
    }

  // TSO/PSO/RMO
  if(tso_pso_rmo || !instrumented)
  {
    // 7 cases

    // (1) (3) (4)
    // if buff0 unused 
    // or buff0 not mine and buff1 unused
    // or buff0 not mine and buff1 not mine
    // -> read from memory (and does not modify the buffer in any aspect)
    const exprt cond_134_expr =
      or_exprt(
        not_exprt( buff0_used_expr ),
        or_exprt(
          and_exprt(
            not_exprt( buff0_thd_expr ),
            not_exprt( buff1_used_expr )
          ),
          and_exprt(
            not_exprt( buff0_thd_expr ),
            not_exprt( buff1_thd_expr )
          )
        )
      );
    const exprt val_134_expr = lhs;
    const exprt buff0_used_134_expr = buff0_used_expr;
    const exprt buff1_used_134_expr = buff1_used_expr;
    const exprt buff0_134_expr = buff0_expr;
    const exprt buff1_134_expr = buff1_expr;
    const exprt buff0_thd_134_expr = buff0_thd_expr;
    const exprt buff1_thd_134_expr = buff1_thd_expr;

    // (2) (6) (7)
    // if buff0 used and mine
    // -> read from buff0
    const exprt cond_267_expr = and_exprt(
      buff0_used_expr,
      buff0_thd_expr
    );
    const exprt val_267_expr =
      buff0_expr;
    const exprt buff0_used_267_expr = false_exprt();
    const exprt buff1_used_267_expr = false_exprt();
    const exprt buff0_267_expr = buff0_expr;
    const exprt buff1_267_expr = buff1_expr;
    const exprt buff0_thd_267_expr = false_exprt();
    const exprt buff1_thd_267_expr = false_exprt();

    // (5)
    // buff0 and buff1 are used, buff0 is not mine, buff1 is mine
    // -> read from buff1
    const exprt cond_5_expr = and_exprt(
      buff0_used_expr,
      and_exprt(
        buff1_used_expr,
        and_exprt(
          not_exprt( buff0_thd_expr ),
          buff1_thd_expr
        )
      )
    );
    const exprt val_5_expr = buff1_expr;
    const exprt buff0_used_5_expr = buff0_used_expr;
    const exprt buff1_used_5_expr = false_exprt();
    const exprt buff0_5_expr = buff0_expr;
    const exprt buff1_5_expr = buff1_expr;
    const exprt buff0_thd_5_expr = buff0_thd_expr;
    const exprt buff1_thd_5_expr = false_exprt();
       
    // Updates
    // memory
    assignment(goto_program, target, location, object, if_exprt(
      cond_134_expr,
      val_134_expr,
      if_exprt(
        cond_267_expr,
        val_267_expr,
        val_5_expr
      )
    ));
    // buff0
    assignment(goto_program, target, location, vars.w_buff0, if_exprt(
      delay_expr,
      buff0_expr,
      if_exprt(
        cond_134_expr,
        buff0_134_expr,
        if_exprt(
          cond_267_expr,
          buff0_267_expr,
          buff0_5_expr
        )
      )
    ));
    // buff1
    assignment(goto_program, target, location, vars.w_buff1, if_exprt(
      delay_expr,
      buff1_expr,
      if_exprt(
        cond_134_expr,
        buff1_134_expr,
        if_exprt(
          cond_267_expr,
          buff1_267_expr,
          buff1_5_expr
        )
      )
    ));
    // buff0_used
    assignment(goto_program, target, location, vars.w_buff0_used, if_exprt(
      delay_expr,
      buff0_used_expr,
      if_exprt(
        cond_134_expr,
        buff0_used_134_expr,
        if_exprt(
          cond_267_expr,
          buff0_used_267_expr,
          buff0_used_5_expr
        )
      )
    ));
    // buff1_used
    assignment(goto_program, target, location, vars.w_buff1_used, if_exprt(
      delay_expr,
      buff1_used_expr,
      if_exprt(
        cond_134_expr,
        buff1_used_134_expr,
        if_exprt(
          cond_267_expr,
          buff1_used_267_expr,
          buff1_used_5_expr
        )
      )
    ));
    // buff0_thd
    assignment(goto_program, target, location, vars.r_buff0_thds[current_thread], if_exprt(
      delay_expr,
      buff0_thd_expr,
      if_exprt(
        cond_134_expr,
        buff0_thd_134_expr,
        if_exprt(
          cond_267_expr,
          buff0_thd_267_expr,
          buff0_thd_5_expr
        )
      )
    ));
    // buff1_thd
    assignment(goto_program, target, location, vars.r_buff1_thds[current_thread], if_exprt(
      delay_expr,
      buff1_thd_expr,
      if_exprt(
        cond_134_expr,
        buff1_thd_134_expr,
        if_exprt(
          cond_267_expr,
          buff1_thd_267_expr,
          buff1_thd_5_expr
        )
      )
    ));

    /*exprt::operandst op;
    optionst options;
    null_message_handlert mess;
    goto_convertt convert(context, options, mess);
    convert.do_output( convert_string_literal("\"IT WORKS\""), convert_string_literal("\"IT WORKS\""), op, goto_program);*/
  }
  // Power
  else
  {
    // a thread can read the other threads' buffers

    // One extra non-deterministic choice needed
    irep_idt choice1=choice("1");
    const symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());
    
    // throw Boolean dice
    assignment(goto_program, target, location, choice1, nondet_bool_expr);

    // 7 cases

    // (1)
    // if buff0 unused 
    // -> read from memory (and does not modify the buffer in any aspect)
    const exprt cond_1_expr = not_exprt( buff0_used_expr );
    const exprt val_1_expr = lhs;
    const exprt buff0_used_1_expr = buff0_used_expr;
    const exprt buff1_used_1_expr = buff1_used_expr;
    const exprt buff0_1_expr = buff0_expr;
    const exprt buff1_1_expr = buff1_expr;
    const exprt buff0_thd_1_expr = buff0_thd_expr;
    const exprt buff1_thd_1_expr = buff1_thd_expr;

    // (2) (6) (7)
    // if buff0 used and mine
    // -> read from buff0
    const exprt cond_267_expr = and_exprt(
        buff0_used_expr,
        buff0_thd_expr
    );
    const exprt val_267_expr = buff0_expr;
    const exprt buff0_used_267_expr = false_exprt();
    const exprt buff1_used_267_expr = false_exprt();
    const exprt buff0_267_expr = buff0_expr;
    const exprt buff1_267_expr = buff1_expr;
    const exprt buff0_thd_267_expr = false_exprt();
    const exprt buff1_thd_267_expr = false_exprt();

    // (3)
    // if buff0 used and not mine, and buff1 not used
    // -> read from buff0 or memory
    const exprt cond_3_expr = and_exprt(
        buff0_used_expr,
        and_exprt(
          not_exprt( buff0_thd_expr ),
          not_exprt( buff1_used_expr )
    ));
    const exprt val_3_expr = if_exprt(
      choice0_expr,
      buff0_expr,
      lhs
    );
    const exprt buff0_used_3_expr = choice0_expr;
    const exprt buff1_used_3_expr = false_exprt();
    const exprt buff0_3_expr = buff0_expr;
    const exprt buff1_3_expr = buff1_expr;
    const exprt buff0_thd_3_expr = false_exprt();
    const exprt buff1_thd_3_expr = false_exprt();

    // (4)
    // buff0 and buff1 are both used, and both not mine
    // -> read from memory or buff0 or buff1
    const exprt cond_4_expr = and_exprt(
      and_exprt(
         buff0_used_expr,
         not_exprt( buff1_thd_expr )
      ),
      and_exprt(
        buff1_used_expr,
        not_exprt( buff0_thd_expr )
      )
    );
    const exprt val_4_expr = if_exprt(
      choice0_expr,
      lhs,
      if_exprt(
        choice1_expr,
        buff0_expr,
        buff1_expr
      )
    );
    const exprt buff0_used_4_expr = or_exprt(
      choice0_expr,
      not_exprt( choice1_expr )
    );
    const exprt buff1_used_4_expr = choice0_expr;
    const exprt buff0_4_expr = buff0_expr;
    const exprt buff1_4_expr = buff1_expr;
    const exprt buff0_thd_4_expr = buff0_thd_expr;
    const exprt buff1_thd_4_expr = if_exprt(
      choice0_expr,
      buff1_thd_expr,
      false_exprt()
    );

    // (5)
    // buff0 and buff1 are both used, and buff0 not mine, and buff1 mine
    // -> read buff1 or buff0
    const exprt cond_5_expr = and_exprt(
      and_exprt(
         buff0_used_expr,
         buff1_thd_expr
      ),
      and_exprt(
        buff1_used_expr,
        not_exprt( buff0_thd_expr )
      )
    );
    const exprt val_5_expr = if_exprt(
      choice0_expr,
      buff1_expr,
      buff0_expr
    );
    const exprt buff0_used_5_expr = choice0_expr;
    const exprt buff1_used_5_expr = false_exprt();
    const exprt buff0_5_expr = buff0_expr;
    const exprt buff1_5_expr = buff1_expr;
    const exprt buff0_thd_5_expr = false_exprt();
    const exprt buff1_thd_5_expr = false_exprt();
      
    // Updates
    // memory
    assignment(goto_program, target, location, object, if_exprt(
      cond_1_expr,
      val_1_expr,
      if_exprt(
        cond_267_expr,
        val_267_expr,
        if_exprt(
          cond_4_expr,
          val_4_expr,
          if_exprt(
            cond_5_expr,
            val_5_expr,
            val_3_expr
          )
        )
      )
    ));
    // buff0
    assignment(goto_program, target, location, vars.w_buff0, if_exprt(
      delay_expr,
      buff0_expr,
      if_exprt(
        cond_1_expr,
        buff0_1_expr,
        if_exprt(
          cond_267_expr,
          buff0_267_expr,
          if_exprt(
            cond_4_expr,
            buff0_4_expr,
            if_exprt(
              cond_5_expr,
              buff0_5_expr,
              buff0_3_expr
            )
          )
        )
      )
    ));
    // buff1
    assignment(goto_program, target, location, vars.w_buff1, if_exprt(
      delay_expr,
      buff1_expr,
      if_exprt(
        cond_1_expr,
        buff1_1_expr,
        if_exprt(
          cond_267_expr,
          buff1_267_expr,
          if_exprt(
            cond_4_expr,
            buff1_4_expr,
            if_exprt(
              cond_5_expr,
              buff1_5_expr,
              buff1_3_expr
            )
          )
        )
      )
    ));
    // buff0_used
    assignment(goto_program, target, location, vars.w_buff0_used, if_exprt(
      delay_expr,
      buff0_used_expr,
      if_exprt(
        cond_1_expr,
        buff0_used_1_expr,
        if_exprt(
          cond_267_expr,
          buff0_used_267_expr,
          if_exprt(
            cond_4_expr,
            buff0_used_4_expr,
            if_exprt(
              cond_5_expr,
              buff0_used_5_expr,
              buff0_used_3_expr
            )
          )
        )
      )
    ));
    // buff1_used
    assignment(goto_program, target, location, vars.w_buff1_used, if_exprt(
      delay_expr,
      buff1_used_expr,
      if_exprt(
        cond_1_expr,
        buff1_used_1_expr,
        if_exprt(
          cond_267_expr,
          buff1_used_267_expr,
          if_exprt(
            cond_4_expr,
            buff1_used_4_expr,
            if_exprt(
              cond_5_expr,
              buff1_used_5_expr,
              buff1_used_3_expr
            )
          )
        )
      )
    ));
    // buff0_thd
    assignment(goto_program, target, location, vars.r_buff0_thds[current_thread], if_exprt(
      delay_expr,
      buff0_thd_expr,
      if_exprt(
        cond_1_expr,
        buff0_thd_1_expr,
        if_exprt(
          cond_267_expr,
          buff0_thd_267_expr,
          if_exprt(
            cond_4_expr,
            buff0_thd_4_expr,
            if_exprt(
              cond_5_expr,
              buff0_thd_5_expr,
              buff0_thd_3_expr
            )
          )
        )
      )
    ));
    // buff1_thd
    assignment(goto_program, target, location, vars.r_buff1_thds[current_thread], if_exprt(
      delay_expr,
      buff1_thd_expr,
      if_exprt(
        cond_1_expr,
        buff1_thd_1_expr,
        if_exprt(
          cond_267_expr,
          buff1_thd_267_expr,
          if_exprt(
            cond_4_expr,
            buff1_thd_4_expr,
            if_exprt(
              cond_5_expr,
              buff1_thd_5_expr,
              buff1_thd_3_expr
            )
          )
        )
      )
    ));
  }
}

/*******************************************************************\

Function: is_buffered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool shared_bufferst::is_buffered(
  const namespacet &ns,
  const symbol_exprt &symbol_expr,
  bool is_write // are we asking for the variable (false), or for the variable and the location in the code? (true)
)
{
  const irep_idt &identifier=symbol_expr.get_identifier();

  if(identifier=="c::__CPROVER_alloc" ||
     identifier=="c::__CPROVER_alloc_size" ||
     identifier=="c::stdin" ||
     identifier=="c::stdout" ||
     identifier=="c::stderr" ||
     identifier=="c::sys_nerr" ||
     has_prefix(id2string(identifier), "__unbuffered_") ||
     has_infix(id2string(identifier), "$tmp_guard") ||
     has_prefix(id2string(identifier), "c::__unbuffered_") )
    return false; // not buffered

  const symbolt &symbol=ns.lookup(identifier);

  if(!symbol.static_lifetime)
    return false; // these are local
    
  if(symbol.thread_local)
    return false; // these are local
   
  if(instrumentations.find(identifier)!=instrumentations.end())
    return false; // these are instrumentations

  return is_buffered_in_general(ns, symbol_expr, is_write);
}

bool shared_bufferst::is_buffered_in_general(
  const namespacet &ns,
  const symbol_exprt &symbol_expr,
  bool is_write // are we asking for the variable (false), or for the variable and the location in the code? (true)
)
{
  const irep_idt &identifier=symbol_expr.get_identifier();
  const locationt &location=symbol_expr.location();

  if(cycles.find(identifier)==cycles.end())
    return false; // not to instrument

  if(!is_write)
  {
    // TO FIX:
    // to be uncommented only when we are sure all the cycles 
    // are detected (before detection of the pairs -- no hack)
    // WARNING: on the FULL cycle, not reduced by PO
    /*typedef std::multimap<irep_idt,locationt>::iterator m_itt;
    std::pair<m_itt,m_itt> ran=cycles_r_loc.equal_range(identifier);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      if(ran_it->second==location)*/
        return true;
  }
  else
  {
    typedef std::multimap<irep_idt,locationt>::iterator m_itt;
    std::pair<m_itt,m_itt> ran=cycles_loc.equal_range(identifier);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      if(ran_it->second==location)
        return true; // not to instrument
  }

  return false;
}

/*******************************************************************\

Function: thread_mark

  Inputs:

 Outputs:

 Purpose: add thread identifier to each instruction

\*******************************************************************/

// TO FIX: this marking is context-insensitive, and does
// not handle recursion yet
void local_thread_mark(
  class contextt &context, goto_functionst &goto_functions,
  goto_programt::instructiont &instruction,
  unsigned* current_thread, unsigned* max_thread, unsigned* coming_from);

unsigned thread_mark(
  class contextt &context,
  goto_functionst &goto_functions)
{
  unsigned current_thread=0;
  unsigned max_thread=0;
  unsigned coming_from=0;

  namespacet ns(context);

  // get "main"
  goto_functionst::function_mapt::iterator
  f_it=goto_functions.function_map.find(goto_functions.main_id());
  
  if(f_it==goto_functions.function_map.end())
    throw "Thread marking needs an entry point";
  
  Forall_goto_program_instructions(i_it, f_it->second.body)
  {
    goto_programt::instructiont &instruction=*i_it;
    local_thread_mark(context, goto_functions, instruction,
      &current_thread,&max_thread,&coming_from);
  }

  return max_thread;
}

void local_thread_mark(
  class contextt &context, goto_functionst &goto_functions, 
  goto_programt::instructiont &instruction, 
  unsigned* current_thread, unsigned* max_thread, unsigned* coming_from)
{
  namespacet ns(context);

  if(instruction.is_start_thread())
  {
    *max_thread=*max_thread+1;
    *coming_from=*current_thread;
    *current_thread=*max_thread;
    instruction.thread=*current_thread;
  }
  else if(instruction.is_end_thread())
    *current_thread=*coming_from;
  else if(instruction.is_function_call())
  {
    const exprt &function=
      to_code_function_call(instruction.code).function();

    if(function.id()==ID_symbol)
    {
      const irep_idt &identifier=
        to_symbol_expr(function).get_identifier();

      // get the function
      goto_functionst::function_mapt::iterator
        f_it=goto_functions.function_map.find(identifier);

      if(f_it==goto_functions.function_map.end())
        throw "Didn't find the function requested";
 
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        goto_programt::instructiont &fun_instruction=*i_it;
        local_thread_mark(context, goto_functions, fun_instruction,
          current_thread,max_thread,coming_from);
      }
    } 
  }

  instruction.thread=*current_thread;
}

/*******************************************************************\

Function: affected_by_delay

  Inputs:

 Outputs:

 Purpose: analysis over the goto-program which computes in 
          affected_by_delay_set the variables (non necessarily
          shared themselves) whose value could be changed as
          effect of a read delay

\*******************************************************************/

void shared_bufferst::affected_by_delay(
  class contextt &context,
  value_setst &value_sets,
  goto_functionst &goto_functions)
{
  namespacet ns(context);

  Forall_goto_functions(f_it, goto_functions)
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      rw_set_loct rw_set(ns, value_sets, i_it);

      forall_rw_set_w_entries(w_it, rw_set)
        forall_rw_set_r_entries(r_it, rw_set)
        {
          std::cout<<"debug: "<<id2string(w_it->second.object)<<" reads from "<<id2string(r_it->second.object)<<std::endl;
          if(is_buffered_in_general(ns, r_it->second.symbol_expr,true)) //shouldn't it be true? false => overapprox
            affected_by_delay_set.insert(w_it->second.object);
        }
    }
}

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose: unwinds loops until 'count'
          Note: doesn't handle concurrency (__CPROVER_ASYNC_) for the
          moment

\*******************************************************************/

void unwind(
    contextt &context,
    goto_programt &body,
    const unsigned count,
    goto_programt &dest)
{
  CFGt cfg(context);
  cfg.initialize(body);

  // from Leo's ai_parseoptions.cpp:
  //
  //in order to get around certain difficulties with loop_info types
  //we apply the strategy of unrolling loops from the deepest most loops down
  //wards

  unsigned max_depth=0;

  {
    loop_infot loop_info(cfg);

    //first get the maximum depth of any loop
    for(std::list<loop_infot::loopt>::const_iterator
        it=loop_info.loops.begin();
        it!=loop_info.loops.end();
        ++it)
      max_depth=std::max(max_depth, it->depth()+1);
  }

  //now count depth up from maxdepth to zero, and unroll loops at that depth
  for( ; max_depth>0; --max_depth)
  {
    loop_infot loop_info(cfg);
    //we can safely unroll sibling without inner loops with the same loop info
    for(std::list<loop_infot::loopt>::const_iterator
        it=loop_info.loops.begin();
        it!=loop_info.loops.end();
        ++it)
      if(it->depth()+1==max_depth)
        cfg.unwind_loop(it->header, loop_info, count);
  }

  cfg.to_goto_program(dest);
}

/*******************************************************************\

Function: lw_sync_fence (Power)

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

inline bool lw_sync_fence(
  value_setst &value_sets,
  contextt &context,
  shared_bufferst &shared_buffers,
  goto_functionst &goto_functions,
  goto_programt &goto_program,
  goto_programt::instructionst::iterator i_it,
  std::set<irep_idt>::iterator s_it,
  goto_programt::instructiont original_instruction
)
{
  namespacet ns(context);

  // spaghetti
  bool leave_early=false;
  bool skip_this_var=false;
  goto_programt::instructionst::iterator next_it=i_it;

  for(; !next_it->is_end_thread()
    && next_it!=(goto_program).instructions.end()
    && !next_it->is_fence()
    && !leave_early 
    && !skip_this_var;
    next_it++)
  {
    rw_set_loct rw_here(ns, value_sets, next_it);
    if(rw_here.empty()) continue;

    forall_rw_set_w_entries(e_it, rw_here)
      if(e_it->second.object== *s_it)
      {
        // Wx => no risk. Exit
        leave_early=true;
        break;
      }

    if(!leave_early)
      forall_rw_set_r_entries(e_it, rw_here)
      {
        if(e_it->second.object==*s_it)
        {
          // Rx => risk of having WxR.
          // Check first before the fence
          goto_programt::instructionst::iterator prev_it=i_it;

          for(; !prev_it->is_start_thread()
            && prev_it!=(goto_program).instructions.begin()
            && !prev_it->is_fence()
            && !skip_this_var;
            prev_it--)
          {
            rw_set_loct rw_there(ns, value_sets, prev_it);
            if(rw_there.empty()) continue;

            forall_rw_set_w_entries(e_it2, rw_here)
            {
              if(e_it2->second.object==*s_it)
              {  
                // WxR in the same thread.
                // Do not flush the buffer of this var
                skip_this_var=true;
                break;
              }

              if(skip_this_var) break;
            }

            if(skip_this_var) break;

            // No Wx before the fence
            // In an interferring thread?
            // FIX: this interferring thread might have already been
            // instrumented...
            Forall_goto_functions(f_it,goto_functions)
            {
              Forall_goto_program_instructions(
                other_thd_it,f_it->second.body)
              {
                // only the other threads
                if(other_thd_it->thread
                  == original_instruction.thread) continue;
                rw_set_loct rw_other_thd(
                  ns, value_sets, other_thd_it);
                if(rw_other_thd.empty()) continue;

                forall_rw_set_w_entries(e_it2, rw_other_thd)
                {
                  if(e_it2->second.object==*s_it)
                  {
                    // WxR in a different thread.
                    // Do not flush the buffer of this var
                    skip_this_var=true;
                    break;
                  }
                }

                if(skip_this_var) break;
              }

              if(skip_this_var) break;
            }
          }
        }

        if(skip_this_var) break;
      }
  }

  if(skip_this_var)
    return true;

  return false;
}

/*******************************************************************\

Function: weak_memory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void shared_bufferst::weak_memory(
  value_setst &value_sets,
  contextt &context,
  goto_programt &goto_program,
  modelt model,
  goto_functionst &goto_functions
)
{
  namespacet ns(context);

  std::set<irep_idt> past_writes;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;
    
    if(instruction.is_assign())
    {
      rw_set_loct rw_set(ns, value_sets, i_it);
      
      if(rw_set.empty()) continue;

      // do not instrument final assertion(s) //?
      bool skip=false;

      /*rw_set_baset::entriest::iterator e_it; 
      for(e_it=rw_set.w_entries.begin(); e_it!=rw_set.w_entries.end(); e_it++)
        if(has_infix(id2string(e_it->second.object), "$tmp_guard")) // except for final assertion(s)
        {
          skip=true;
          break;
        }*/

//#define WITHFENCE // instruments the guards of the fences
#ifndef WITHFENCE
      if(skip)
        continue;
#endif

      // add all the written values (which are not instrumentations)
      // in a set
      forall_rw_set_w_entries(w_it, rw_set)
        if(is_buffered(ns, w_it->second.symbol_expr,false))//true))
        //{ std::cout<<"+++ thread"<<instruction.thread<<": "
        //<<id2string(w_it->second.symbol_expr.get_identifier())<<" is inserted for fences"<<std::endl;
          past_writes.insert(w_it->second.object);//}
      
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const locationt &location=original_instruction.location;

      // we make the whole thing atomic      
      instruction.make_atomic_begin();
      instruction.location=location;
      i_it++;

      //
#ifdef WITHFENCE
      if(skip)
      { 
        for(std::set<irep_idt>::iterator pw_it=past_writes.begin(); pw_it!=past_writes.end(); pw_it++)
          det_flush(//
            goto_program, i_it, location, *pw_it,
            original_instruction.thread);

        forall_rw_set_w_entries(e_it, rw_set)
          assignment(//
            goto_program, i_it, location,
            e_it->second.object, original_instruction.code.op1());

        // ATOMIC_END
        i_it=goto_program.insert_before(i_it);
        i_it->make_atomic_end();
        i_it->location=location;
        i_it++;
      
        i_it--; 
        continue;
      }
#endif
      
      // we first perform (non-deterministically) up to 2 writes for
      // stuff that is potentially read
      //if(!skip)
      forall_rw_set_r_entries(e_it, rw_set)
      {
        // flush read
        //shared_buffers.flush_read(
          //goto_program, i_it, location, e_it->second.object);

        if(is_buffered(ns, e_it->second.symbol_expr,false)) //ONLY?//
          nondet_flush(
            goto_program, i_it, location, e_it->second.object,
            original_instruction.thread, (model==TSO || model==PSO || model==RMO));
      }

      // Now perform the write(s).
      forall_rw_set_w_entries(e_it, rw_set)
      {
        // if one of the previous read was to buffer, then delays the read
        //if(!skip)
        if(model==RMO || model==POWER)
        forall_rw_set_r_entries(r_it, rw_set)
          if(is_buffered(ns, r_it->second.symbol_expr,true))
          {
            delay_read(
              goto_program, i_it, location, r_it->second.object, e_it->second.object);
            //break;
          }

        if(is_buffered(ns, e_it->second.symbol_expr,true))
        {
          //if(!skip)
          write(
            goto_program, i_it, location, 
            e_it->second.object,original_instruction,
            original_instruction.thread);
        }
        else
        {
          // unbuffered

          if(model==RMO || model==Power)
            forall_rw_set_r_entries(r_it, rw_set)
              if(affected_by_delay_set.find(r_it->second.object)!=affected_by_delay_set.end() )
              {      
                const varst &vars=(*this)(r_it->second.object);  

                std::cout<<"writer "<<e_it->second.object<<" reads "<<r_it->second.object<<std::endl;

                // TO FIX: how to deal with rhs including calls?
                // if a read is delayed, use its alias instead of itself -- or not
                symbol_exprt to_replace_expr = symbol_exprt( r_it->second.object, vars.type);
                symbol_exprt new_read_expr = symbol_exprt( vars.read_delayed_var,
                pointer_typet(vars.type));
                symbol_exprt read_delayed_expr = symbol_exprt( vars.read_delayed, bool_typet());

                // One extra non-deterministic choice needed
                irep_idt choice1=choice("1");
                const symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());
                const exprt nondet_bool_expr=side_effect_expr_nondett(bool_typet());

                // throw Boolean dice
                assignment(goto_program, i_it, location, choice1, nondet_bool_expr);

                exprt rhs = if_exprt( 
                read_delayed_expr, 
                if_exprt(
                  choice1_expr,
                  dereference_exprt(new_read_expr,vars.type),
                  to_replace_expr),
                to_replace_expr);//original_instruction.code.op1());
        
                assignment(
                  goto_program, i_it, location,
                  r_it->second.object, rhs);
              }

          // normal assignment
          assignment(
            goto_program, i_it, location, 
            e_it->second.object, original_instruction.code.op1());
        
          // TO FIX: do we really want to constrain this way?
          // if this variable is buffered somewhere else, makes sure the buffer is emptied before
          /*const varst &vars=(*this)(e_it->second.object);
          assignment(
            goto_program, i_it, location,
            vars.w_buff0_used, false_exprt());
          assignment(
            goto_program, i_it, location,
            vars.w_buff1_used, false_exprt());
          for(unsigned cnt=0; cnt<nb_threads; cnt++)
          {
            assignment(
              goto_program, i_it, location,
              vars.r_buff0_thds[cnt], false_exprt());
           assignment(
              goto_program, i_it, location,
              vars.r_buff1_thds[cnt], false_exprt());
          }*/ //////
        }
      }

      // if last writes was flushed to make the lhs reads the buffer but without affecting the memory,
      // restore the previous memory value (buffer flush delay)
      //if(!skip)
      forall_rw_set_r_entries(e_it, rw_set)
        if(is_buffered(ns, e_it->second.symbol_expr,false))
        {
          const varst vars= (*this)(e_it->second.object);
          const exprt delayed_expr=symbol_exprt(vars.flush_delayed, bool_typet());
          const symbol_exprt mem_value_expr=symbol_exprt(vars.mem_tmp, vars.type);
          const exprt cond_expr=if_exprt(delayed_expr, mem_value_expr,
            e_it->second.symbol_expr);

          assignment(
            goto_program, i_it, location,
            e_it->second.object, cond_expr);
          assignment(
            goto_program, i_it, location,
            vars.flush_delayed, false_exprt());
        }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->location=location;
      i_it++;
        
      i_it--; // the for loop already counts us up
    }
    else if(instruction.is_fence())// || (instruction.is_lwfence() && model==Power))
    {
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const locationt &location=original_instruction.location;

      // ATOMIC_BEGIN
      instruction.make_atomic_begin();
      instruction.location=location;
      i_it++;

      // does it for all the previous statements
      for(std::set<irep_idt>::iterator s_it=past_writes.begin(); 
        s_it!=past_writes.end(); s_it++)
      {
        if(instruction.is_lwfence())
          if(lw_sync_fence(value_sets, context, *this,
            goto_functions, 
            goto_program, i_it, s_it, original_instruction))
            continue;

        det_flush(
          goto_program, i_it, location, *s_it,
          original_instruction.thread);
      }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->location=location;
      i_it++;
      
      i_it--; // the for loop already counts us up
    }    
    else if(instruction.is_lwfence())
    {
      // po -- remove the lwfence
      i_it->make_skip();
    }

  }
  remove_skip(goto_program);  
}

/*******************************************************************\

Function: introduce_temporaries

  Inputs:

 Outputs:

 Purpose: all access to shared variables is pushed into assignments

\*******************************************************************/

void introduce_temporaries(
  value_setst &value_sets,
  contextt &context,
  const irep_idt &function,
  goto_programt &goto_program)
{
  namespacet ns(context);
  unsigned tmp_counter=0;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    std::cout<<instruction.location<<std::endl;

    if(instruction.is_goto() ||
       instruction.is_assert() ||
       instruction.is_assume())
    {
      rw_set_loct rw_set(ns, value_sets, i_it);
      if(rw_set.empty()) continue;
      
      symbolt new_symbol;
      new_symbol.base_name="$tmp_guard";
      new_symbol.name=id2string(function)+"$tmp_guard"+i2string(tmp_counter++);
      new_symbol.type=bool_typet();
      new_symbol.static_lifetime=true;
      new_symbol.thread_local=true;
      new_symbol.value.make_nil();
      
      symbol_exprt symbol_expr=::symbol_expr(new_symbol);
      
      symbolt *symbol_ptr;
      context.move(new_symbol, symbol_ptr);
      
      goto_programt::instructiont new_i;
      new_i.make_assignment();
      new_i.code=code_assignt(symbol_expr, instruction.guard);
      new_i.location=instruction.location;
      new_i.function=instruction.function;

      // replace guard
      instruction.guard=symbol_expr;
      goto_program.insert_before_swap(i_it, new_i);

      i_it++; // step forward
    }
    else if(instruction.is_function_call())
    {
      // TODO
    }
  }
}

/*******************************************************************\

Function: extract_my_events

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<int> extract_my_events()
{
  std::ifstream file;
  file.open("inst.evt");
  std::set<int> this_set;

  int size;
  file >> size;
  
  int tmp;

  for(unsigned i=0; i<size; i++)
  {
    file>>tmp;
    this_set.insert(tmp);
  }

  file.close();

  return this_set;
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
  modelt model,
  const bool one_partition,
  const bool one_event_per_cycle,
  const bool my_events,
  const unsigned unwinding_bound)
{
  // get rid of pointers
  remove_pointers(goto_functions, context, value_sets);

  // all access to shared variables is pushed into assignments
  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=ID_main)
    introduce_temporaries(value_sets, context, f_it->first, f_it->second.body);

  // unwind the loops k times
  if(0!=unwinding_bound)
    Forall_goto_functions(f_it, goto_functions)
      if(f_it->first!=ID_main && f_it->first!="c::"+config.main)
      {
        goto_programt prog;

        unwind(context, f_it->second.body, unwinding_bound, prog); 

        f_it->second.body.swap(prog);
      }

  unsigned max_thds=thread_mark(context,goto_functions);

  // EXPERIMENTAL: cycle detection using ugly C toy tool -- yeurk
  event_grapht graph;
  graph.convert_prg(value_sets,context,goto_functions, model);

  // collects cycles and the instructions to instrument
  if(model==TSO)
  {
    graph.collect_cycles_tso(one_partition);
    graph.to_instrument_tso();
  }
  else if(model==PSO)
  {
    graph.collect_cycles_pso(one_partition);
    graph.to_instrument_pso();
  }
  else if(model==RMO)
  {
    graph.collect_cycles_rmo(one_partition);
    graph.to_instrument_rmo();
  }
  else
  {
    graph.collect_cycles_power(one_partition);
    graph.to_instrument_power();
  }

  // all the events per cycle, only one, or my events?
  if(my_events)
  {
    std::set<int> events_set = extract_my_events();
    graph.instrument_my_events(events_set);
  }  
  else if(one_event_per_cycle)
    graph.instrument_one_event_per_cycle();
  else
    graph.instrument_all();

  // now adds buffers
  shared_bufferst shared_buffers(context,max_thds);

  // stores the events to instrument
  shared_buffers.cycles=graph.var_to_instr; // var in the cycles
  shared_buffers.cycles_loc=graph.id_to_loc; // instrumented places
  shared_buffers.cycles_r_loc=graph.id_to_cyc_loc; // places in the cycles

  // for reads delays
  shared_buffers.affected_by_delay(context,value_sets,goto_functions);

  for(std::set<irep_idt>::iterator it=shared_buffers.affected_by_delay_set.begin(); 
    it!=shared_buffers.affected_by_delay_set.end();
    it++)
    std::cout<<id2string(*it)<<std::endl;

  std::cout<<std::endl<<"I instrument:"<<std::endl;
  for(std::set<irep_idt>::iterator it=shared_buffers.cycles.begin(); 
    it!=shared_buffers.cycles.end(); it++)
  {
    typedef std::multimap<irep_idt,locationt>::iterator m_itt;
    const std::pair<m_itt,m_itt> ran=
      shared_buffers.cycles_loc.equal_range(*it);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      std::cout<<((*it)==""?"fence":*it)<<", "<<ran_it->second<<std::endl;
  }

  std::cout<<"shared buffer created"<<std::endl;

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
       f_it->first!=ID_main)
      shared_buffers.weak_memory(value_sets, context, f_it->second.body, 
        //shared_buffers, 
        model, goto_functions
      );

  // initialization code for buffers
  shared_buffers.add_initialization_code(goto_functions);
  
  // update counters etc.
  goto_functions.update();
}
#endif

/*******************************************************************\

Function: weak_memory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void weak_memory(
  weak_memory_modelt model,
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions,
  bool one_partition,
  bool one_event_per_cycle,
  bool my_events,
  unsigned unwinding_bound)
{
//  weak_memory(value_sets, context, goto_functions, model, 
//    one_partition, one_event_per_cycle, my_events, unwinding_bound);
}
