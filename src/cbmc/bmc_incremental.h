 /*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C  HDL

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

 \*******************************************************************/

#ifndef CPROVER_CBMC_BMC_INCREMENTAL_H
#define CPROVER_CBMC_BMC_INCREMENTAL_H

#include <list>
#include <map>

#include <util/options.h>

#include <solvers/prop/prop_conv.h>
#include <goto-symex/symex_target_equation.h>

#include "symex_bmc_incremental.h"
#include "bv_cbmc.h"
#include "bmc.h"

class bmc_incrementalt:public bmct
{
public:
  bmc_incrementalt(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt& _prop_conv,
    const goto_functionst &_goto_functions):
    bmct(
      _options,
      _symbol_table,
      _prop_conv,
      _message_handler),
    goto_functions(_goto_functions)
  {
    symex_ptr=new symex_bmc_incrementalt(ns, new_symbol_table, equation);
    symex().constant_propagation=options.get_bool_option("propagation");
  }

  virtual ~bmc_incrementalt() { }

  // make public
  virtual resultt run() { return run(goto_functions); }
  virtual resultt initialize() { return bmct::initialize(); }
  virtual resultt step() { return step(goto_functions); }

protected:
  const goto_functionst &goto_functions;

  // ENHANCE: move this into symex_bmc
  goto_symext::statet symex_state;

  // overload
  virtual resultt run(const goto_functionst &goto_functions);
  virtual resultt step(const goto_functionst &goto_functions);

  // unwinding
  virtual void setup_unwind();

 private:
  symex_bmc_incrementalt &symex()
  {
    return dynamic_cast<symex_bmc_incrementalt &>(*symex_ptr);
  }
};

#endif
