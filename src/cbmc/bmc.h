/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>

#include <util/hash_cont.h>
#include <util/options.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>
#include <langapi/language_ui.h>
#include <goto-symex/symex_target_equation.h>
#include <goto-programs/safety_checker.h>

#include "symex_bmc.h"

class bmct:public safety_checkert
{
public:
  bmct(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt& _prop_conv):
    safety_checkert(ns, _message_handler),
    options(_options),
    ns(_symbol_table, new_symbol_table),
    equation(ns),
    symex(ns, new_symbol_table, equation),
    prop_conv(_prop_conv),
    ui(ui_message_handlert::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
  }
 
  virtual resultt run(const goto_functionst &goto_functions);
  virtual ~bmct() { }

  // additional stuff   
  expr_listt bmc_constraints;  
  
  friend class cbmc_satt;
  friend class hw_cbmc_satt;
  friend class counterexample_beautification_greedyt;
  
  void set_ui(language_uit::uit _ui) { ui=_ui; }

  // the safety_checkert interface
  virtual resultt operator()(
    const goto_functionst &goto_functions)
  {
    return run(goto_functions);
  }

protected:
  const optionst &options;  
  symbol_tablet new_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  symex_bmct symex;
  prop_convt &prop_conv;

  // use gui format
  language_uit::uit ui;
  
  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);
    
  virtual resultt decide(
    const goto_functionst &,
    prop_convt &);
    
  // unwinding
  virtual void setup_unwind();

  virtual void do_unwind_module(
    decision_proceduret &decision_procedure);
  void do_conversion(prop_convt &solver);
  
  virtual void show_vcc();
  virtual resultt all_properties(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual void show_vcc(std::ostream &out);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace();
  
  bool cover(
    const goto_functionst &goto_functions,
    prop_convt &solver,
    const std::string &criterion);

  friend class bmc_all_propertiest;
  friend class bmc_covert;
};

#endif
