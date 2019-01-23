/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs

#include "race_check.h"

#include <goto-programs/remove_skip.h>

#include <linking/static_lifetime_init.h>

#include "rw_set.h"

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#define L_M_ARG(x) x,
#define L_M_LAST_ARG(x) , x
#else
#define L_M_ARG(x)
#define L_M_LAST_ARG(x)
#endif

class w_guardst
{
public:
  explicit w_guardst(symbol_tablet &_symbol_table):symbol_table(_symbol_table)
  {
  }

  std::list<irep_idt> w_guards;

  const symbolt &get_guard_symbol(const irep_idt &object);

  const exprt get_guard_symbol_expr(const irep_idt &object)
  {
    return get_guard_symbol(object).symbol_expr();
  }

  const exprt get_w_guard_expr(const rw_set_baset::entryt &entry)
  {
    return get_guard_symbol_expr(entry.object);
  }

  const exprt get_assertion(const rw_set_baset::entryt &entry)
  {
    return not_exprt(get_guard_symbol_expr(entry.object));
  }

  void add_initialization(goto_programt &goto_program) const;

protected:
  symbol_tablet &symbol_table;
};

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
  new_symbol.value=false_exprt();

  symbolt *symbol_ptr;
  symbol_table.move(new_symbol, symbol_ptr);
  return *symbol_ptr;
}

void w_guardst::add_initialization(goto_programt &goto_program) const
{
  goto_programt::targett t=goto_program.instructions.begin();
  const namespacet ns(symbol_table);

  for(std::list<irep_idt>::const_iterator
      it=w_guards.begin();
      it!=w_guards.end();
      it++)
  {
    exprt symbol=ns.lookup(*it).symbol_expr();

    t=goto_program.insert_before(t);
    t->type=ASSIGN;
    t->code=code_assignt(symbol, false_exprt());

    t++;
  }
}

static std::string comment(const rw_set_baset::entryt &entry, bool write)
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

static bool is_shared(const namespacet &ns, const symbol_exprt &symbol_expr)
{
  const irep_idt &identifier=symbol_expr.get_identifier();

  if(identifier==CPROVER_PREFIX "alloc" ||
     identifier==CPROVER_PREFIX "alloc_size" ||
     identifier=="stdin" ||
     identifier=="stdout" ||
     identifier=="stderr" ||
     identifier=="sys_nerr" ||
     has_prefix(id2string(identifier), "symex::invalid_object") ||
     has_prefix(id2string(identifier), "symex_dynamic::dynamic_object"))
    return false; // no race check

  const symbolt &symbol=ns.lookup(identifier);
  return symbol.is_shared();
}

static bool has_shared_entries(const namespacet &ns, const rw_set_baset &rw_set)
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

// clang-format off
// clang-format is confused by the L_M_ARG macro and wants to indent the line
// after
static void race_check(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  const irep_idt &function_id,
  L_M_ARG(const goto_functionst::goto_functiont &goto_function)
  goto_programt &goto_program,
  w_guardst &w_guards)
// clang-format on
{
  namespacet ns(symbol_table);

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_function);
#endif

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_assign())
    {
      rw_set_loct rw_set(
        ns, value_sets, function_id, i_it L_M_LAST_ARG(local_may));

      if(!has_shared_entries(ns, rw_set))
        continue;

      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);

      instruction.make_skip();
      i_it++;

      // now add assignments for what is written -- set
      forall_rw_set_w_entries(e_it, rw_set)
      {
        if(!is_shared(ns, e_it->second.symbol_expr))
          continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->type=ASSIGN;
        t->code=code_assignt(
          w_guards.get_w_guard_expr(e_it->second),
          e_it->second.guard);

        t->source_location=original_instruction.source_location;
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
        if(!is_shared(ns, e_it->second.symbol_expr))
          continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->type=ASSIGN;
        t->code=code_assignt(
          w_guards.get_w_guard_expr(e_it->second),
          false_exprt());

        t->source_location=original_instruction.source_location;
        i_it=++t;
      }

      // now add assertions for what is read and written
      forall_rw_set_r_entries(e_it, rw_set)
      {
        if(!is_shared(ns, e_it->second.symbol_expr))
          continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->make_assertion(w_guards.get_assertion(e_it->second));
        t->source_location=original_instruction.source_location;
        t->source_location.set_comment(comment(e_it->second, false));
        i_it=++t;
      }

      forall_rw_set_w_entries(e_it, rw_set)
      {
        if(!is_shared(ns, e_it->second.symbol_expr))
          continue;

        goto_programt::targett t=goto_program.insert_before(i_it);

        t->make_assertion(w_guards.get_assertion(e_it->second));
        t->source_location=original_instruction.source_location;
        t->source_location.set_comment(comment(e_it->second, true));
        i_it=++t;
      }

      i_it--; // the for loop already counts us up
    }
  }

  remove_skip(goto_program);
}

void race_check(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  const irep_idt &function_id,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program)
{
  w_guardst w_guards(symbol_table);

  race_check(
    value_sets,
    symbol_table,
    function_id,
    L_M_ARG(goto_function) goto_program,
    w_guards);

  w_guards.add_initialization(goto_program);
  goto_program.update();
}

void race_check(
  value_setst &value_sets,
  goto_modelt &goto_model)
{
  w_guardst w_guards(goto_model.symbol_table);

  Forall_goto_functions(f_it, goto_model.goto_functions)
    if(f_it->first!=goto_functionst::entry_point() &&
       f_it->first != INITIALIZE_FUNCTION)
      race_check(
        value_sets,
        goto_model.symbol_table,
        f_it->first,
        L_M_ARG(f_it->second) f_it->second.body,
        w_guards);

  // get "main"
  goto_functionst::function_mapt::iterator
    m_it=goto_model.goto_functions.function_map.find(
      goto_model.goto_functions.entry_point());

  if(m_it==goto_model.goto_functions.function_map.end())
    throw "race check instrumentation needs an entry point";

  goto_programt &main=m_it->second.body;
  w_guards.add_initialization(main);
  goto_model.goto_functions.update();
}
