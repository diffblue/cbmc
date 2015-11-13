/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_SYMEX_BMC_INCREMENTAL_ONE_LOOP_H
#define CPROVER_CBMC_SYMEX_BMC_INCREMENTAL_ONE_LOOP_H

#include <limits>

#include <util/hash_cont.h>
#include <util/message.h>

#include <solvers/prop/prop_conv.h>

#include "symex_bmc.h"

class symex_bmc_incremental_one_loopt:
  public symex_bmct
{
public:
  symex_bmc_incremental_one_loopt(
    const namespacet &_ns,
    symbol_tablet &_new_symbol_table,
    symex_targett &_target,
    prop_convt& _prop_conv)
  :
  symex_bmct(_ns, _new_symbol_table, _target),
  ignore_assertions(false),
  incr_loop_id(""),
  incr_max_unwind(std::numeric_limits<unsigned>::max()),
  incr_min_unwind(0),
  prop_conv(_prop_conv)
  {}

  bool ignore_assertions;
  irep_idt incr_loop_id;
  unsigned incr_max_unwind;
  unsigned incr_min_unwind;
 
protected:  
  // incremental unwinding
  prop_convt& prop_conv;
 
  // returns true if the symbolic execution is to be interrupted for checking
  virtual bool check_break(const irep_idt &id, 
                           bool is_function, 
                           goto_symext::statet& state, 
                           const exprt &cond, 
                           unsigned unwind);

  // for loop unwinding
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    unsigned unwind);
};

#endif
