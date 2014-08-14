/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_SYMEX_BMC_H
#define CPROVER_CBMC_SYMEX_BMC_H

#include <util/hash_cont.h>
#include <util/message.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>
#include <solvers/prop/prop_conv.h>
#include <util/decision_procedure.h>
#include <langapi/language_ui.h>

class symex_bmct:
  public goto_symext,
  public messaget
{
public:
  symex_bmct(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target,
    prop_convt& _prop_conv);

  // To show progress
  irept last_location;

  // Control unwinding.

  bool is_incremental;
  irep_idt incr_loop_id;
  unsigned incr_max_unwind;
  unsigned incr_min_unwind;

  bool add_loop_check();
  void update_loop_info(bool fully_unwound);
  
  void set_unwind_limit(unsigned limit)
  {
    max_unwind=limit;
    max_unwind_is_set=true;
  }
  
  void set_unwind_thread_loop_limit(
    unsigned thread_nr,
    const irep_idt &id,
    unsigned limit)
  {
    thread_loop_limits[thread_nr][id]=limit;
  }

  prop_convt& prop_conv;

  void set_ui(language_uit::uit _ui) { ui=_ui; }

  void set_unwind_loop_limit(
    const irep_idt &id,
    unsigned limit)
  {
    loop_limits[id]=limit;
  }

protected:  
  // use gui format
  language_uit::uit ui;

  // incremental unwinding

  // returns true if the symbolic execution is to be interrupted for checking
  virtual bool check_break(const irep_idt &id, 
                           bool is_function, 
                           statet& state, 
                           const exprt &cond, 
                           unsigned unwind);

  // stores info to check whether loop has been fully unwound
  typedef struct {
    irep_idt id;
    exprt guard;
    exprt cond;
    goto_symex_statet::framet::loop_infot *loop_info;
    symex_targett::sourcet source;
    bool checked_function;
  } loop_condt;

  loop_condt loop_cond;

  // We have
  // 1) a global limit (max_unwind)
  // 2) a limit per loop, all threads
  // 3) a limit for a particular thread.
  // We use the most specific of the above.

  unsigned max_unwind;
  bool max_unwind_is_set;

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> loop_limitst;
  loop_limitst loop_limits;
  
  typedef std::map<unsigned, loop_limitst> thread_loop_limitst;
  thread_loop_limitst thread_loop_limits;

  //
  // overloaded from goto_symext
  //
  virtual bool symex_step(
    const goto_functionst &goto_functions,
    statet &state);

  // for loop unwinding
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    const unsigned thread_nr,
    unsigned unwind);
    
  virtual void no_body(const irep_idt &identifier);
  
  hash_set_cont<irep_idt, irep_id_hash> body_warnings;
};

#endif
