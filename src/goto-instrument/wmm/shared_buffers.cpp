/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "shared_buffers.h"

#include <util/c_types.h>

#include <linking/static_lifetime_init.h>

#include <goto-instrument/rw_set.h>

#include "fence.h"

/// returns a unique id (for fresh variables)
std::string shared_bufferst::unique(void)
{
  message.debug()<<"$fresh#"+std::to_string(uniq)<<messaget::eom;
  return "$fresh#"+std::to_string(uniq++);
}

/// instruments the variable
const shared_bufferst::varst &shared_bufferst::operator()(
  const irep_idt &object)
{
  var_mapt::const_iterator it=var_map.find(object);
  if(it!=var_map.end())
    return it->second;

  varst &vars=var_map[object];

  namespacet ns(symbol_table);
  const symbolt &symbol=ns.lookup(object);

  vars.type=symbol.type;

  vars.w_buff0=add(object, symbol.base_name, "$w_buff0", symbol.type);
  vars.w_buff1=add(object, symbol.base_name, "$w_buff1", symbol.type);

  vars.w_buff0_used=add(object, symbol.base_name, "$w_buff0_used",
    bool_typet());
  vars.w_buff1_used=add(object, symbol.base_name, "$w_buff1_used",
    bool_typet());

  vars.mem_tmp=add(object, symbol.base_name, "$mem_tmp", symbol.type);
  vars.flush_delayed=add(object, symbol.base_name, "$flush_delayed",
    bool_typet());

  vars.read_delayed=
    add(object, symbol.base_name, "$read_delayed", bool_typet());
  vars.read_delayed_var=
    add(
      object,
      symbol.base_name,
      "$read_delayed_var",
      pointer_type(symbol.type));

  for(unsigned cnt=0; cnt<nb_threads; cnt++)
  {
    vars.r_buff0_thds.push_back(
      shared_bufferst::add(
        object,
        symbol.base_name,
        "$r_buff0_thd"+std::to_string(cnt),
        bool_typet()));
    vars.r_buff1_thds.push_back(
      shared_bufferst::add(
        object,
        symbol.base_name,
        "$r_buff1_thd"+std::to_string(cnt),
        bool_typet()));
  }

  return vars;
}

/// add a new var for instrumenting the input var
/// \par parameters: var, suffix, type of the var, added as an instrumentation
/// \return identifier of the new var
irep_idt shared_bufferst::add(
  const irep_idt &object,
  const irep_idt &base_name,
  const std::string &suffix,
  const typet &type,
  bool instrument)
{
  const irep_idt identifier=id2string(object)+suffix;

  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.base_name=id2string(base_name)+suffix;
  new_symbol.type=type;
  new_symbol.is_static_lifetime=true;
  new_symbol.value.make_nil();

  if(instrument)
    instrumentations.insert(identifier);

  symbolt *symbol_ptr;
  symbol_table.move(new_symbol, symbol_ptr);
  return identifier;
}

void shared_bufferst::add_initialization(goto_programt &goto_program)
{
  goto_programt::targett t=goto_program.instructions.begin();
  const namespacet ns(symbol_table);

  for(const auto &vars : var_map)
  {
    source_locationt source_location;
    source_location.make_nil();

    assignment(goto_program, t, source_location, vars.second.w_buff0_used,
      false_exprt());
    assignment(goto_program, t, source_location, vars.second.w_buff1_used,
      false_exprt());
    assignment(goto_program, t, source_location, vars.second.flush_delayed,
      false_exprt());
    assignment(goto_program, t, source_location, vars.second.read_delayed,
      false_exprt());
    assignment(goto_program, t, source_location, vars.second.read_delayed_var,
      null_pointer_exprt(pointer_type(vars.second.type)));

    for(const auto &id : vars.second.r_buff0_thds)
      assignment(goto_program, t, source_location, id, false_exprt());

    for(const auto &id : vars.second.r_buff1_thds)
      assignment(goto_program, t, source_location, id, false_exprt());
  }
}

void shared_bufferst::add_initialization_code(
  goto_functionst &goto_functions)
{
  // get "main"
  goto_functionst::function_mapt::iterator
    m_it=goto_functions.function_map.find(goto_functions.entry_point());

  if(m_it==goto_functions.function_map.end())
    throw "weak memory instrumentation needs an entry point";

  goto_programt &main=m_it->second.body;
  add_initialization(main);
}

/// add an assignment in the goto-program
void shared_bufferst::assignment(
  goto_programt &goto_program,
  goto_programt::targett &t,
  const source_locationt &source_location,
  const irep_idt &id_lhs,
  const exprt &value)
{
  const namespacet ns(symbol_table);
  std::string identifier=id2string(id_lhs);

  const size_t pos=identifier.find("[]");

  if(pos!=std::string::npos)
  {
    /* we don't distinguish the members of an array for the moment */
    identifier.erase(pos);
  }

  try
  {
    const exprt symbol=ns.lookup(identifier).symbol_expr();

    t=goto_program.insert_before(t);
    t->type=ASSIGN;
    t->code=code_assignt(symbol, value);
    t->code.add_source_location()=source_location;
    t->source_location=source_location;

    // instrumentations.insert((const irep_idt) (t->code.id()));

    t++;
  }
  catch(const std::string &s)
  {
    message.warning() << s << messaget::eom;
  }
}

/// delays a read (POWER)
void shared_bufferst::delay_read(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const source_locationt &source_location,
  const irep_idt &read_object,
  const irep_idt &write_object)
{
/* option 1: */
/* trick using an additional variable whose value is to be defined later */

#if 0
  assignment(goto_program, target, source_location, vars.read_delayed,
             true_exprt());
  assignment(goto_program, target, source_location, vars.read_delayed_var,
    read_object);

  const irep_idt &new_var=add_fresh_var(write_object, unique(), vars.type);

  assignment(goto_program, target, source_location, vars.read_new_var, new_var);

  // initial write, but from the new variable now
  assignment(goto_program, target, source_location, write_object, new_var);
#endif

/* option 2 */
/* pointer */

  const std::string identifier=id2string(write_object);

  message.debug()<<"delay_read: " << messaget::eom;
  const varst &vars=(*this)(write_object);

  const symbol_exprt read_object_expr=symbol_exprt(read_object, vars.type);

  assignment(
    goto_program,
    target,
    source_location,
    vars.read_delayed,
    true_exprt());
  assignment(
    goto_program,
    target,
    source_location,
    vars.read_delayed_var,
    address_of_exprt(read_object_expr));
}

/// flushes read (POWER)
void shared_bufferst::flush_read(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const source_locationt &source_location,
  const irep_idt &write_object)
{
#if 0
  // option 1
  const varst &vars=(*this)(write_object);

  const symbol_exprt fresh_var_expr=symbol_exprt(vars.read_new_var, vars.type);
  const symbol_exprt var_expr=symbol_exprt(vars.read_delayed_var, vars.type);
  const exprt eq_expr=equal_exprt(var_expr, fresh_var_expr);

  const symbol_exprt cond_delayed_expr=symbol_exprt(vars.read_delayed,
    bool_typet());
  const exprt if_expr=if_exprt(cond_delayed_expr, eq_expr, true_exprt());

  target=goto_program.insert_before(target);
  target->type=ASSUME;
  target->guard=if_expr;
  target->guard.source_location()=source_location;
  target->source_location=source_location;

  target++;

  assignment(goto_program, target, source_location, vars.read_delayed,
             false_exprt());
#else
  // option 2: do nothing
  // unused parameters
  (void)goto_program;
  (void)target;
  (void)target;
  (void)source_location;
  (void)write_object;
#endif
}

/// instruments write
void shared_bufferst::write(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const source_locationt &source_location,
  const irep_idt &object,
  goto_programt::instructiont &original_instruction,
  const unsigned current_thread)
{
  const std::string identifier=id2string(object);

  message.debug() << "write: " << object << messaget::eom;
  const varst &vars=(*this)(object);

  // We rotate the write buffers for anything that is written.
  assignment(goto_program, target, source_location, vars.w_buff1, vars.w_buff0);
  assignment(
    goto_program, target, source_location, vars.w_buff0,
    original_instruction.code.op1());

  // We update the used flags
  assignment(
    goto_program,
    target,
    source_location,
    vars.w_buff1_used,
    vars.w_buff0_used);
  assignment(
    goto_program,
    target,
    source_location,
    vars.w_buff0_used,
    true_exprt());

  // We should not exceed the buffer size -- inserts assertion for dynamically
  // checking this
  const exprt buff0_used_expr=symbol_exprt(vars.w_buff0_used, bool_typet());
  const exprt buff1_used_expr=symbol_exprt(vars.w_buff1_used, bool_typet());
  const exprt cond_expr=
    not_exprt(and_exprt(buff1_used_expr, buff0_used_expr));

  target=goto_program.insert_before(target);
  target->guard=cond_expr;
  target->type=ASSERT;
  target->code=code_assertt();
  target->code.add_source_location()=source_location;
  target->source_location=source_location;
  target++;

  // We update writers ownership of the values in the buffer
  for(unsigned cnt=0; cnt<nb_threads; cnt++)
    assignment(goto_program, target, source_location, vars.r_buff1_thds[cnt],
      vars.r_buff0_thds[cnt]);

  // We update the lucky new author of this value in the buffer
  assignment(
    goto_program,
    target,
    source_location,
    vars.r_buff0_thds[current_thread],
    true_exprt());
}

/// flush buffers (instruments fence)
void shared_bufferst::det_flush(
  goto_programt &goto_program,
  goto_programt::targett &target,
  const source_locationt &source_location,
  const irep_idt &object,
  const unsigned current_thread)
{
  const std::string identifier=id2string(object);

  // mostly for instrumenting the fences. A thread only flushes the values it
  // wrote in the buffer.
  message.debug() << "det flush: " << messaget::eom;
  const varst &vars=(*this)(object);

  // current value in the memory
  const exprt lhs=symbol_exprt(object, vars.type);

  // if buff0 from this thread, uses it to update the memory (the most recent
  // value, or last write by -ws-> ); if not, if buff1 from this thread, uses
  // it; if not, keeps the current memory value
  const exprt buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
  const exprt buff1_expr=symbol_exprt(vars.w_buff1, vars.type);

  const exprt buff0_used_expr=symbol_exprt(vars.w_buff0_used, bool_typet());
  const exprt buff1_used_expr=symbol_exprt(vars.w_buff1_used, bool_typet());

  const exprt buff0_mine_expr=symbol_exprt(vars.r_buff0_thds[current_thread],
    bool_typet());
  const exprt buff1_mine_expr=symbol_exprt(vars.r_buff1_thds[current_thread],
    bool_typet());

  const exprt buff0_used_and_mine_expr=and_exprt(buff0_used_expr,
    buff0_mine_expr);
  const exprt buff1_used_and_mine_expr=and_exprt(buff1_used_expr,
    buff1_mine_expr);

  const exprt new_value_expr=
    if_exprt(
      buff0_used_and_mine_expr,
      buff0_expr,
      if_exprt(
        buff1_used_and_mine_expr,
        buff1_expr,
        lhs));

  // We update (or not) the value in the memory
  assignment(goto_program, target, source_location, object, new_value_expr);

  // We update the flags of the buffer
  // if buff0 used and mine, then it is no more used, as we flushed the last
  // write and -ws-> imposes not to have other writes in the buffer
  assignment(
    goto_program,
    target,
    source_location,
    vars.w_buff0_used,
    if_exprt(
      buff0_used_and_mine_expr,
      false_exprt(),
      buff0_used_expr));

  // buff1 used and mine & not buff0 used and mine, then it no more used
  // if buff0 is used and mine, then, by ws, buff1 is no more used
  // otherwise, remains as it is
  const exprt buff0_or_buff1_used_and_mine_expr=
    or_exprt(buff0_used_and_mine_expr, buff1_used_and_mine_expr);

  assignment(
    goto_program,
    target,
    source_location,
    vars.w_buff1_used,
    if_exprt(
      buff0_or_buff1_used_and_mine_expr,
      false_exprt(),
      buff1_used_expr));

  // We update the ownerships
  // if buff0 mine and used, flushed, so belongs to nobody
  const exprt buff0_thd_expr=
    symbol_exprt(vars.r_buff0_thds[current_thread], bool_typet());

  assignment(
    goto_program,
    target,
    source_location,
    vars.r_buff0_thds[current_thread],
    if_exprt(buff0_used_and_mine_expr, false_exprt(), buff0_thd_expr));

  // if buff1 used and mine, or if buff0 used and mine, then buff1 flushed and
  // doesn't belong to anybody
  const exprt buff1_thd_expr=
    symbol_exprt(vars.r_buff1_thds[current_thread], bool_typet());

  assignment(
    goto_program,
    target,
    source_location,
    vars.r_buff1_thds[current_thread],
    if_exprt(
      buff0_or_buff1_used_and_mine_expr,
      false_exprt(),
      buff1_thd_expr));
}

/// instruments read
void shared_bufferst::nondet_flush(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &target,
  const source_locationt &source_location,
  const irep_idt &object,
  const unsigned current_thread,
  const bool tso_pso_rmo) // true: tso/pso/rmo; false: power
{
  const std::string identifier=id2string(object);

  message.debug() << "nondet flush: " << object << messaget::eom;

  try
  {
  const varst &vars=(*this)(object);

  // Non deterministic choice
  irep_idt choice0 = choice(function_id, "0");
  irep_idt choice2 = choice(function_id, "2"); // delays the write flush

  const symbol_exprt choice0_expr=symbol_exprt(choice0, bool_typet());
  const symbol_exprt delay_expr=symbol_exprt(choice2, bool_typet());
  const exprt nondet_bool_expr =
    side_effect_expr_nondett(bool_typet(), source_location);

  // throw Boolean dice
  assignment(goto_program, target, source_location, choice0, nondet_bool_expr);
  assignment(goto_program, target, source_location, choice2, nondet_bool_expr);

  // Buffers and memory
  const symbol_exprt buff0_expr=symbol_exprt(vars.w_buff0, vars.type);
  const symbol_exprt buff1_expr=symbol_exprt(vars.w_buff1, vars.type);
  const exprt lhs=symbol_exprt(object, vars.type);

  // Buffer uses
  const symbol_exprt buff0_used_expr=symbol_exprt(vars.w_buff0_used,
    bool_typet());
  const symbol_exprt buff1_used_expr=symbol_exprt(vars.w_buff1_used,
    bool_typet());

  // Buffer ownerships
  const symbol_exprt buff0_thd_expr=
    symbol_exprt(vars.r_buff0_thds[current_thread], bool_typet());
  const symbol_exprt buff1_thd_expr=
    symbol_exprt(vars.r_buff1_thds[current_thread], bool_typet());


  // Will the write be directly flushed, or is it just a read?
  assignment(
    goto_program, target, source_location, vars.flush_delayed, delay_expr);
  assignment(goto_program, target, source_location, vars.mem_tmp, lhs);

  // for POWER, only instrumented reads can read from the buffers of other
  // threads
  bool instrumented=false;

  if(!tso_pso_rmo)
  {
    if(cycles.find(object)!=cycles.end())
    {
      typedef std::multimap<irep_idt, source_locationt>::iterator m_itt;
      std::pair<m_itt, m_itt> ran=cycles_loc.equal_range(object);
      for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
        if(ran_it->second==source_location)
        {
          instrumented=true;
          break;
        }
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
    const exprt cond_134_expr=
      or_exprt(
        not_exprt(buff0_used_expr),
        or_exprt(
          and_exprt(
            not_exprt(buff0_thd_expr),
            not_exprt(buff1_used_expr)),
          and_exprt(
            not_exprt(buff0_thd_expr),
            not_exprt(buff1_thd_expr))));
    const exprt val_134_expr=lhs;
    const exprt buff0_used_134_expr=buff0_used_expr;
    const exprt buff1_used_134_expr=buff1_used_expr;
    const exprt buff0_134_expr=buff0_expr;
    const exprt buff1_134_expr=buff1_expr;
    const exprt buff0_thd_134_expr=buff0_thd_expr;
    const exprt buff1_thd_134_expr=buff1_thd_expr;

    // (2) (6) (7)
    // if buff0 used and mine
    // -> read from buff0
    const exprt cond_267_expr=and_exprt(buff0_used_expr, buff0_thd_expr);
    const exprt val_267_expr=buff0_expr;
    const exprt buff0_used_267_expr=false_exprt();
    const exprt buff1_used_267_expr=false_exprt();
    const exprt buff0_267_expr=buff0_expr;
    const exprt buff1_267_expr=buff1_expr;
    const exprt buff0_thd_267_expr=false_exprt();
    const exprt buff1_thd_267_expr=false_exprt();

    // (5)
    // buff0 and buff1 are used, buff0 is not mine, buff1 is mine
    // -> read from buff1
    const exprt cond_5_expr=
      and_exprt(
        buff0_used_expr,
        and_exprt(
          buff1_used_expr,
          and_exprt(not_exprt(buff0_thd_expr), buff1_thd_expr)));
    const exprt val_5_expr=buff1_expr;
    const exprt buff0_used_5_expr=buff0_used_expr;
    const exprt buff1_used_5_expr=false_exprt();
    const exprt buff0_5_expr=buff0_expr;
    const exprt buff1_5_expr=buff1_expr;
    const exprt buff0_thd_5_expr=buff0_thd_expr;
    const exprt buff1_thd_5_expr=false_exprt();

    // Updates
    // memory
    assignment(
      goto_program,
      target,
      source_location,
      object,
      if_exprt(
        cond_134_expr,
        val_134_expr,
        if_exprt(
          cond_267_expr,
          val_267_expr,
          val_5_expr)));
    // buff0
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff0,
      if_exprt(
        delay_expr,
        buff0_expr,
        if_exprt(
          cond_134_expr,
          buff0_134_expr,
          if_exprt(
            cond_267_expr,
            buff0_267_expr,
            buff0_5_expr))));
    // buff1
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff1,
      if_exprt(
        delay_expr,
        buff1_expr,
        if_exprt(
          cond_134_expr,
          buff1_134_expr,
          if_exprt(
            cond_267_expr,
            buff1_267_expr,
            buff1_5_expr))));
    // buff0_used
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff0_used,
      if_exprt(
        delay_expr,
        buff0_used_expr,
        if_exprt(
          cond_134_expr,
          buff0_used_134_expr,
          if_exprt(
            cond_267_expr,
            buff0_used_267_expr,
            buff0_used_5_expr))));
    // buff1_used
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff1_used,
      if_exprt(
        delay_expr,
        buff1_used_expr,
        if_exprt(
          cond_134_expr,
          buff1_used_134_expr,
          if_exprt(
            cond_267_expr,
            buff1_used_267_expr,
            buff1_used_5_expr))));
    // buff0_thd
    assignment(
      goto_program,
      target,
      source_location,
      vars.r_buff0_thds[current_thread],
      if_exprt(
        delay_expr,
        buff0_thd_expr,
        if_exprt(
          cond_134_expr,
          buff0_thd_134_expr,
          if_exprt(
            cond_267_expr,
            buff0_thd_267_expr,
            buff0_thd_5_expr))));
    // buff1_thd
    assignment(
      goto_program,
      target,
      source_location,
      vars.r_buff1_thds[current_thread], if_exprt(
        delay_expr,
        buff1_thd_expr,
        if_exprt(
          cond_134_expr,
          buff1_thd_134_expr,
          if_exprt(
            cond_267_expr,
            buff1_thd_267_expr,
            buff1_thd_5_expr))));
  }
  // POWER
  else
  {
    // a thread can read the other threads' buffers

    // One extra non-deterministic choice needed
    irep_idt choice1 = choice(function_id, "1");
    const symbol_exprt choice1_expr=symbol_exprt(choice1, bool_typet());

    // throw Boolean dice
    assignment(
      goto_program, target, source_location, choice1, nondet_bool_expr);

    // 7 cases

    // (1)
    // if buff0 unused
    // -> read from memory (and does not modify the buffer in any aspect)
    const exprt cond_1_expr=not_exprt(buff0_used_expr);
    const exprt val_1_expr=lhs;
    const exprt buff0_used_1_expr=buff0_used_expr;
    const exprt buff1_used_1_expr=buff1_used_expr;
    const exprt buff0_1_expr=buff0_expr;
    const exprt buff1_1_expr=buff1_expr;
    const exprt buff0_thd_1_expr=buff0_thd_expr;
    const exprt buff1_thd_1_expr=buff1_thd_expr;

    // (2) (6) (7)
    // if buff0 used and mine
    // -> read from buff0
    const exprt cond_267_expr=
      and_exprt(buff0_used_expr, buff0_thd_expr);
    const exprt val_267_expr=buff0_expr;
    const exprt buff0_used_267_expr=false_exprt();
    const exprt buff1_used_267_expr=false_exprt();
    const exprt buff0_267_expr=buff0_expr;
    const exprt buff1_267_expr=buff1_expr;
    const exprt buff0_thd_267_expr=false_exprt();
    const exprt buff1_thd_267_expr=false_exprt();

    // (3)
    // if buff0 used and not mine, and buff1 not used
    // -> read from buff0 or memory
    const exprt cond_3_expr=
      and_exprt(
        buff0_used_expr,
        and_exprt(
          not_exprt(buff0_thd_expr),
          not_exprt(buff1_used_expr)));
    const exprt val_3_expr=if_exprt(choice0_expr, buff0_expr, lhs);
    const exprt buff0_used_3_expr=choice0_expr;
    const exprt buff1_used_3_expr=false_exprt();
    const exprt buff0_3_expr=buff0_expr;
    const exprt buff1_3_expr=buff1_expr;
    const exprt buff0_thd_3_expr=false_exprt();
    const exprt buff1_thd_3_expr=false_exprt();

    // (4)
    // buff0 and buff1 are both used, and both not mine
    // -> read from memory or buff0 or buff1
    const exprt cond_4_expr=
      and_exprt(
        and_exprt(buff0_used_expr, not_exprt(buff1_thd_expr)),
        and_exprt(buff1_used_expr, not_exprt(buff0_thd_expr)));
    const exprt val_4_expr=
      if_exprt(
        choice0_expr,
        lhs,
        if_exprt(
          choice1_expr,
          buff0_expr,
          buff1_expr));
    const exprt buff0_used_4_expr=
      or_exprt(choice0_expr, not_exprt(choice1_expr));
    const exprt buff1_used_4_expr=choice0_expr;
    const exprt buff0_4_expr=buff0_expr;
    const exprt buff1_4_expr=buff1_expr;
    const exprt buff0_thd_4_expr=buff0_thd_expr;
    const exprt buff1_thd_4_expr=
      if_exprt(choice0_expr, buff1_thd_expr, false_exprt());

    // (5)
    // buff0 and buff1 are both used, and buff0 not mine, and buff1 mine
    // -> read buff1 or buff0
    const exprt cond_5_expr=
      and_exprt(
        and_exprt(buff0_used_expr, buff1_thd_expr),
        and_exprt(buff1_used_expr, not_exprt(buff0_thd_expr)));
    const exprt val_5_expr=
      if_exprt(
        choice0_expr,
        buff1_expr,
        buff0_expr);
    const exprt buff0_used_5_expr=choice0_expr;
    const exprt buff1_used_5_expr=false_exprt();
    const exprt buff0_5_expr=buff0_expr;
    const exprt buff1_5_expr=buff1_expr;
    const exprt buff0_thd_5_expr=false_exprt();
    const exprt buff1_thd_5_expr=false_exprt();

    // Updates
    // memory
    assignment(
      goto_program,
      target,
      source_location,
      object,
      if_exprt(
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
              val_3_expr)))));
    // buff0
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff0,
      if_exprt(
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
                buff0_3_expr))))));
    // buff1
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff1,
      if_exprt(
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
                buff1_3_expr))))));
    // buff0_used
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff0_used,
      if_exprt(
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
                buff0_used_3_expr))))));
    // buff1_used
    assignment(
      goto_program,
      target,
      source_location,
      vars.w_buff1_used,
      if_exprt(
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
                buff1_used_3_expr))))));
    // buff0_thd
    assignment(
      goto_program,
      target,
      source_location,
      vars.r_buff0_thds[current_thread],
      if_exprt(
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
                buff0_thd_3_expr))))));
    // buff1_thd
    assignment(
      goto_program,
      target,
      source_location,
      vars.r_buff1_thds[current_thread],
      if_exprt(
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
                buff1_thd_3_expr))))));
  }
  }
  catch(const std::string &s)
  {
    message.warning() << s << messaget::eom;
  }
}

bool shared_bufferst::is_buffered(
  const namespacet &ns,
  const symbol_exprt &symbol_expr,
  bool is_write
  // are we asking for the variable (false), or for the variable and
  // the source_location in the code (true)
)
{
  const irep_idt &identifier=symbol_expr.get_identifier();

  if(identifier==CPROVER_PREFIX "alloc" ||
     identifier==CPROVER_PREFIX "alloc_size" ||
     identifier=="stdin" ||
     identifier=="stdout" ||
     identifier=="stderr" ||
     identifier=="sys_nerr" ||
     has_prefix(id2string(identifier), "__unbuffered_") ||
     has_prefix(id2string(identifier), "__CPROVER"))
    return false; // not buffered

  const symbolt &symbol=ns.lookup(identifier);

  if(!symbol.is_static_lifetime)
    return false; // these are local

  if(symbol.is_thread_local)
    return false; // these are local

  if(instrumentations.find(identifier)!=instrumentations.end())
    return false; // these are instrumentations

  return is_buffered_in_general(symbol_expr, is_write);
}

bool shared_bufferst::is_buffered_in_general(
  const symbol_exprt &symbol_expr,
  bool is_write
  // are we asking for the variable (false), or for the variable and the
  // source_location in the code? (true)
)
{
  if(cav11)
    return true;

  const irep_idt &identifier=symbol_expr.get_identifier();
  const source_locationt &source_location=symbol_expr.source_location();

  if(cycles.find(identifier)==cycles.end())
    return false; // not to instrument

  if(!is_write)
  {
    // to be uncommented only when we are sure all the cycles
    // are detected (before detection of the pairs -- no hack)
    // WARNING: on the FULL cycle, not reduced by PO
    /*typedef std::multimap<irep_idt,source_locationt>::iterator m_itt;
    std::pair<m_itt,m_itt> ran=cycles_r_loc.equal_range(identifier);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      if(ran_it->second==source_location)*/
        return true;
  }
  else
  {
    typedef std::multimap<irep_idt, source_locationt>::iterator m_itt;
    std::pair<m_itt, m_itt> ran=cycles_loc.equal_range(identifier);
    for(m_itt ran_it=ran.first; ran_it!=ran.second; ran_it++)
      if(ran_it->second==source_location)
        return true; // not to instrument
  }

  return false;
}

/// analysis over the goto-program which computes in affected_by_delay_set the
/// variables (non necessarily shared themselves) whose value could be changed
/// as effect of a read delay
void shared_bufferst::affected_by_delay(
  value_setst &value_sets,
  goto_functionst &goto_functions)
{
  namespacet ns(symbol_table);

  Forall_goto_functions(f_it, goto_functions)
  {
#ifdef LOCAL_MAY
    local_may_aliast local_may(f_it->second);
#endif

    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
        rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
        , local_may
#endif
        ); // NOLINT(whitespace/parens)
        forall_rw_set_w_entries(w_it, rw_set)
          forall_rw_set_r_entries(r_it, rw_set)
          {
            message.debug() <<"debug: "<<id2string(w_it->second.object)
              <<" reads from "<<id2string(r_it->second.object)
              <<messaget::eom;
            if(is_buffered_in_general(r_it->second.symbol_expr, true))
              // shouldn't it be true? false => overapprox
              affected_by_delay_set.insert(w_it->second.object);
          }
    }
  }
}

/// instruments the program for the pairs detected through the CFG
void shared_bufferst::cfg_visitort::weak_memory(
  value_setst &value_sets,
  const irep_idt &function_id,
  memory_modelt model)
{
  shared_buffers.message.debug()
    << "visit function " << function_id << messaget::eom;
  if(function_id == INITIALIZE_FUNCTION)
    return;

  namespacet ns(symbol_table);
  goto_programt &goto_program = goto_functions.function_map[function_id].body;

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_functions.function_map[function_id]);
#endif

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    shared_buffers.message.debug() << "instruction "<<instruction.type
                                   << messaget::eom;

    /* thread marking */
    if(instruction.is_start_thread())
    {
      max_thread=max_thread+1;
      coming_from=current_thread;
      current_thread=max_thread;
    }
    else if(instruction.is_end_thread())
      current_thread=coming_from;

    if(instruction.is_assign())
    {
      try
      {
        rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
        , local_may
#endif
        ); // NOLINT(whitespace/parens)

        if(rw_set.empty())
          continue;

        // add all the written values (which are not instrumentations)
        // in a set
        forall_rw_set_w_entries(w_it, rw_set)
          if(shared_buffers.is_buffered(ns, w_it->second.symbol_expr, false))
            past_writes.insert(w_it->second.object);

        goto_programt::instructiont original_instruction;
        original_instruction.swap(instruction);
        const source_locationt &source_location=
          original_instruction.source_location;

        // ATOMIC_BEGIN: we make the whole thing atomic
        instruction.make_atomic_begin();
        instruction.source_location=source_location;
        i_it++;

        // we first perform (non-deterministically) up to 2 writes for
        // stuff that is potentially read
        forall_rw_set_r_entries(e_it, rw_set)
        {
          // flush read -- do nothing in this implementation
          shared_buffers.flush_read(
            goto_program, i_it, source_location, e_it->second.object);

          if(shared_buffers.is_buffered(ns, e_it->second.symbol_expr, false))
            shared_buffers.nondet_flush(
              function_id,
              goto_program,
              i_it,
              source_location,
              e_it->second.object,
              current_thread,
              (model == TSO || model == PSO || model == RMO));
        }

        // Now perform the write(s).
        forall_rw_set_w_entries(e_it, rw_set)
        {
          // if one of the previous read was to buffer, then delays the read
          if(model==RMO || model==Power)
          {
            forall_rw_set_r_entries(r_it, rw_set)
              if(shared_buffers.is_buffered(ns, r_it->second.symbol_expr, true))
              {
                shared_buffers.delay_read(
                  goto_program, i_it, source_location, r_it->second.object,
                  e_it->second.object);
              }
          }

          if(shared_buffers.is_buffered(ns, e_it->second.symbol_expr, true))
          {
            shared_buffers.write(
              goto_program, i_it, source_location,
              e_it->second.object, original_instruction,
              current_thread);
          }
          else
          {
            // unbuffered
            if(model==RMO || model==Power)
            {
              forall_rw_set_r_entries(r_it, rw_set)
                if(shared_buffers.affected_by_delay_set.find(
                    r_it->second.object)!=
                   shared_buffers.affected_by_delay_set.end())
                {
                  shared_buffers.message.debug() << "second: "
                    << r_it->second.object << messaget::eom;
                  const varst &vars=(shared_buffers)(r_it->second.object);

                  shared_buffers.message.debug() << "writer "
                    <<e_it->second.object
                    <<" reads "<<r_it->second.object<< messaget::eom;

                  // TO FIX: how to deal with rhs including calls?
                  // if a read is delayed, use its alias instead of itself
                  // -- or not
                  symbol_exprt to_replace_expr=symbol_exprt(
                    r_it->second.object, vars.type);
                  symbol_exprt new_read_expr=symbol_exprt(
                    vars.read_delayed_var,
                    pointer_type(vars.type));
                  symbol_exprt read_delayed_expr=symbol_exprt(
                    vars.read_delayed, bool_typet());

                  // One extra non-deterministic choice needed
                  irep_idt choice1 = shared_buffers.choice(function_id, "1");
                  const symbol_exprt choice1_expr=symbol_exprt(choice1,
                    bool_typet());
                  const exprt nondet_bool_expr =
                    side_effect_expr_nondett(bool_typet(), source_location);

                  // throw Boolean dice
                  shared_buffers.assignment(
                    goto_program,
                    i_it,
                    source_location,
                    choice1,
                    nondet_bool_expr);

                  const if_exprt rhs(
                    read_delayed_expr,
                    if_exprt(
                      choice1_expr,
                      dereference_exprt(new_read_expr, vars.type),
                      to_replace_expr),
                    to_replace_expr); // original_instruction.code.op1());

                  shared_buffers.assignment(
                    goto_program, i_it, source_location,
                    r_it->second.object, rhs);
                }
            }

            // normal assignment
            shared_buffers.assignment(
              goto_program, i_it, source_location,
              e_it->second.object, original_instruction.code.op1());
          }
        }

        // if last writes was flushed to make the lhs reads the buffer but
        // without affecting the memory, restore the previous memory value
        // (buffer flush delay)
        forall_rw_set_r_entries(e_it, rw_set)
          if(shared_buffers.is_buffered(ns, e_it->second.symbol_expr, false))
          {
            shared_buffers.message.debug() << "flush restore: "
              << e_it->second.object << messaget::eom;
            const varst vars= (shared_buffers)(e_it->second.object);
            const exprt delayed_expr=symbol_exprt(vars.flush_delayed,
              bool_typet());
            const symbol_exprt mem_value_expr=symbol_exprt(vars.mem_tmp,
              vars.type);
            const exprt cond_expr=if_exprt(delayed_expr, mem_value_expr,
              e_it->second.symbol_expr);

            shared_buffers.assignment(
              goto_program, i_it, source_location,
              e_it->second.object, cond_expr);
            shared_buffers.assignment(
              goto_program, i_it, source_location,
              vars.flush_delayed, false_exprt());
          }

        // ATOMIC_END
        i_it=goto_program.insert_before(i_it);
        i_it->make_atomic_end();
        i_it->source_location=source_location;
        i_it++;

        i_it--; // the for loop already counts us up
      }
      catch (...)
      {
        shared_buffers.message.warning() << "Identifier not found"
          << messaget::eom;
      }
    }
    else if(is_fence(instruction, ns) ||
            (instruction.is_other() &&
             instruction.code.get_statement()==ID_fence &&
             (instruction.code.get_bool("WRfence") ||
              instruction.code.get_bool("WWfence") ||
              instruction.code.get_bool("RWfence") ||
              instruction.code.get_bool("RRfence"))))
    {
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);
      const source_locationt &source_location=
        original_instruction.source_location;

      // ATOMIC_BEGIN
      instruction.make_atomic_begin();
      instruction.source_location=source_location;
      i_it++;

      // does it for all the previous statements
      for(std::set<irep_idt>::iterator s_it=past_writes.begin();
        s_it!=past_writes.end(); s_it++)
      {
        shared_buffers.det_flush(
          goto_program, i_it, source_location, *s_it,
          current_thread);
      }

      // ATOMIC_END
      i_it=goto_program.insert_before(i_it);
      i_it->make_atomic_end();
      i_it->source_location=source_location;
      i_it++;

      i_it--; // the for loop already counts us up
    }
    else if(is_lwfence(instruction, ns))
    {
      // po -- remove the lwfence
      i_it->make_skip();
    }
    else if(instruction.is_function_call())
    {
      const exprt &fun=to_code_function_call(instruction.code).function();
      weak_memory(value_sets, to_symbol_expr(fun).get_identifier(), model);
    }
  }
}
