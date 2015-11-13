 /*******************************************************************\
 
Module: Incremental Bounded Model Checking for ANSI-C  HDL
 
Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com
 
 \*******************************************************************/
 
#ifndef CPROVER_CBMC_BMC_INCREMENTAL_ONE_LOOP_H
#define CPROVER_CBMC_BMC_INCREMENTAL_ONE_LOOP_H
 
#if 1
#include <iostream>
#endif

 #include <list>
 #include <map>
 
 #include <util/hash_cont.h>
 #include <util/options.h>
 
 #include <solvers/prop/prop_conv.h>
 #include <goto-symex/symex_target_equation.h>
 
#include "symex_bmc_incremental_one_loop.h"
 #include "bv_cbmc.h"
#include "bmc.h"
#include <goto-symex/memory_model.h>
 
class bmc_incremental_one_loopt : public bmct
{
 public:
  bmc_incremental_one_loopt(
     const optionst &_options,
     const symbol_tablet &_symbol_table,
     message_handlert &_message_handler,
     prop_convt& _prop_conv,
     const goto_functionst &_goto_functions)
   :
   bmct(_options,_symbol_table,_message_handler,_prop_conv,
	new symex_bmc_incremental_one_loopt(ns, new_symbol_table, 
					    equation, prop_conv)),
   goto_functions(_goto_functions),
   symex(dynamic_cast<symex_bmc_incremental_one_loopt &>(*symex_ptr))  
   { }
 
  virtual resultt initialize();
  virtual resultt step();
  virtual resultt run();
  virtual resultt run(const goto_functionst &goto_functions) 
  { return run(); }
  virtual ~bmc_incremental_one_loopt() {}
 
 protected:
  const goto_functionst &goto_functions;
  std::unique_ptr<memory_model_baset> memory_model;
  goto_symext::statet symex_state; //TODO: move this into symex_bmc
 
  virtual resultt decide(
     const goto_functionst &goto_functions,
     prop_convt &prop_conv) 
  { return decide(goto_functions, prop_conv,true); } 
 
  virtual resultt decide(
     const goto_functionst &goto_functions,
     prop_convt &, 
     bool show_report);
     
   // unwinding
   virtual void setup_unwind();
 private:
  symex_bmc_incremental_one_loopt &symex;
};
 
#endif
