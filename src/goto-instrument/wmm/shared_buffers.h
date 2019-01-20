/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_GOTO_INSTRUMENT_WMM_SHARED_BUFFERS_H
#define CPROVER_GOTO_INSTRUMENT_WMM_SHARED_BUFFERS_H

#include <map>
#include <set>

#include <goto-programs/goto_program.h>
#include <util/namespace.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/message.h>

#include "wmm.h"

class symbol_tablet;
class goto_functionst;
class value_setst;

class shared_bufferst
{
public:
  shared_bufferst(symbol_tablet &_symbol_table, unsigned _nb_threads,
    messaget &_message):
    symbol_table(_symbol_table),
    nb_threads(_nb_threads+1),
    uniq(0),
    cav11(false),
    message(_message)
  {
  }

  void set_cav11(memory_modelt model)
  {
    if(model!=TSO)
      throw "sorry, CAV11 only available for TSO";
    cav11 = true;
  }

  /* instrumentation of a variable */
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
    // affecting the memory (Note: we model lhs := rhs by rhs := ..., then
    // lhs := rhs)
    irep_idt mem_tmp;
    irep_idt flush_delayed;

    // Thread: Was it me who wrote at this place?
    std::vector<irep_idt> r_buff0_thds, r_buff1_thds;

    // for delayed read:
    irep_idt read_delayed;
    irep_idt read_delayed_var;

    typet type;
  };

  typedef std::map<irep_idt, varst> var_mapt;
  var_mapt var_map;

  /* instructions in violation cycles (to instrument): */
  // variables in the cycles
  std::set<irep_idt> cycles;
  // events instrumented: var->locations in the code
  std::multimap<irep_idt, source_locationt> cycles_loc;
  // events in cycles: var->locations (for read instrumentations)
  std::multimap<irep_idt, source_locationt> cycles_r_loc;

  const varst &operator()(const irep_idt &object);

  void add_initialization_code(goto_functionst &goto_functions);

  void delay_read(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &read_object,
    const irep_idt &write_object);

  void flush_read(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &write_object);

  void write(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &object,
    goto_programt::instructiont &original_instruction,
    const unsigned current_thread);

  void det_flush(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &object,
    const unsigned current_thread);

  void nondet_flush(
    const irep_idt &function_id,
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &object,
    const unsigned current_thread,
    const bool tso_pso_rmo);

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &id_lhs,
    const exprt &rhs);

  void assignment(
    goto_programt &goto_program,
    goto_programt::targett &t,
    const source_locationt &source_location,
    const irep_idt &id_lhs,
    const irep_idt &id_rhs)
  {
    namespacet ns(symbol_table);
    assignment(goto_program, t, source_location, id_lhs,
      ns.lookup(id_rhs).symbol_expr());
  }

  bool track(const irep_idt &id) const
  {
    namespacet ns(symbol_table);

    const symbolt &symbol=ns.lookup(id);
    if(symbol.is_thread_local)
      return false;
    if(has_prefix(id2string(id), CPROVER_PREFIX))
      return false;

    return true;
  }

  irep_idt choice(const irep_idt &function_id, const std::string &suffix)
  {
    const auto maybe_symbol = symbol_table.lookup(function_id);
    const std::string function_base_name =
      maybe_symbol
        ? id2string(maybe_symbol->base_name)
        : "main";
    return add(function_base_name+"_weak_choice",
      function_base_name+"_weak_choice", suffix, bool_typet());
  }

  bool is_buffered(
    const namespacet&,
    const symbol_exprt&,
    bool is_write);

  bool is_buffered_in_general(
    const symbol_exprt&,
    bool is_write);

  void weak_memory(
    value_setst &value_sets,
    symbol_tablet &symbol_table,
    goto_programt &goto_program,
    memory_modelt model,
    goto_functionst &goto_functions);

  void affected_by_delay(
    value_setst &value_sets,
    goto_functionst &goto_functions);

  class cfg_visitort
  {
  protected:
    shared_bufferst &shared_buffers;
    symbol_tablet &symbol_table;
    goto_functionst &goto_functions;

    /* for thread marking (dynamic) */
    unsigned current_thread;
    unsigned coming_from;
    unsigned max_thread;

    /* data propagated through the CFG */
    std::set<irep_idt> past_writes;

  public:
    cfg_visitort(shared_bufferst &_shared, symbol_tablet &_symbol_table,
      goto_functionst &_goto_functions)
      :shared_buffers(_shared), symbol_table(_symbol_table),
        goto_functions(_goto_functions)
    {
      current_thread = 0;
      coming_from = 0;
      max_thread = 0;
    }

    void weak_memory(
      value_setst &value_sets,
      const irep_idt &function_id,
      memory_modelt model);
  };

protected:
  class symbol_tablet &symbol_table;

  // number of threads interfering
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

  bool cav11;

  /* message */
  messaget &message;

  irep_idt add(
    const irep_idt &object,
    const irep_idt &base_name,
    const std::string &suffix,
    const typet &type,
    bool added_as_instrumentation);

  irep_idt add(
    const irep_idt &object,
    const irep_idt &base_name,
    const std::string &suffix,
    const typet &type)
  {
    return add(object, base_name, suffix, type, true);
  }

  /* inserting a non-instrumenting, fresh variable */
  irep_idt add_fresh_var(
    const irep_idt &object,
    const irep_idt &base_name,
    const std::string &suffix,
    const typet &type)
  {
    return add(object, base_name, suffix, type, false);
  }

  void add_initialization(goto_programt &goto_program);
};

#endif // CPROVER_GOTO_INSTRUMENT_WMM_SHARED_BUFFERS_H
