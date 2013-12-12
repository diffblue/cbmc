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
    symex_target_equationt &_target,
    prop_convt& _prop_conv);

  // To show progress
  irept last_location;

  // control unwinding  
  unsigned long max_unwind;
  std::map<irep_idt, long> unwind_set;
  irep_idt incr_loop_id;
  unsigned long incr_max_unwind;
  unsigned long incr_min_unwind;

  prop_convt& prop_conv;

  void convert();

  literalt current_activation_literal();

  void set_ui(language_uit::uit _ui) { ui=_ui; }

protected:  
  // for incremental unwinding and checking
  symex_target_equationt::SSA_stepst::iterator loop_last_SSA_step; //TODO: probably not needed in future

  typedef std::map<irep_idt,symbol_exprt> symbol_mapt;

  //  symbol_mapt get_last_symbol_assignments(); //TODO to be removed
  //  void freeze_variables(symbol_mapt& last_symbol_assignments); //TODO to be removed

  // use gui format
  language_uit::uit ui;

  virtual bool check_break(const symex_targett::sourcet &source, unsigned unwind);

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
    unsigned unwind);
    
  virtual void no_body(const irep_idt &identifier);
  
  hash_set_cont<irep_idt, irep_id_hash> body_warnings;
};

#endif
