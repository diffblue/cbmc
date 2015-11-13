/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_SYMEX_BMC_INCREMENTAL_H
#define CPROVER_CBMC_SYMEX_BMC_INCREMENTAL_H
 
#include "symex_bmc.h"
 
class symex_bmc_incrementalt : public symex_bmct
{
 public:
  symex_bmc_incrementalt(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target);

  unsigned incr_max_unwind;
  unsigned incr_min_unwind;

  bool add_loop_check();
  void update_loop_info(bool fully_unwound);
  
protected:  
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

#if 1
  std::set<unsigned> magic_numbers;
#endif

  // for loop unwinding
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);

  virtual bool get_unwind_recursion(
    const irep_idt &identifier,
    const unsigned thread_nr,
    unsigned unwind);
};

#endif
