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

#include "symex_bmc.h"
#include "bv_cbmc.h"


class bmct:public messaget
{
public:
  bmct(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt& _prop_conv):
    messaget(_message_handler),
    options(_options),
    ns(_symbol_table, new_symbol_table),
    equation(ns),
    symex(ns, new_symbol_table, equation,_prop_conv),
    ui(ui_message_handlert::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
  }
 
  virtual bool run(const goto_functionst &goto_functions);
  virtual ~bmct() { }

  // additional stuff   
  expr_listt bmc_constraints;  
  
  friend class cbmc_satt;
  friend class hw_cbmc_satt;
  friend class counterexample_beautification_greedyt;
  
  void set_ui(language_uit::uit _ui) { ui=_ui; }
  
protected:
  const optionst &options;  
  symbol_tablet new_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  symex_bmct symex;
 
  // use gui format
  language_uit::uit ui;
  
  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);
    
  virtual bool decide(prop_convt &prop_conv);
    
  virtual bool write_dimacs(prop_convt& bv_cbmc);
  virtual bool write_dimacs(prop_convt& bv_cbmc, std::ostream &out);
  
  // unwinding
  virtual void setup_unwind();

  virtual void do_unwind_module(
    decision_proceduret &decision_procedure);
  void do_conversion(prop_convt &solver);

  virtual void show_vcc();
  virtual void show_vcc(std::ostream &out);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace(
    const prop_convt &prop_conv);
  
  // vacuity checks
  void cover_assertions(const goto_functionst &goto_functions);

  // all claims
  struct goalt
  {
    bvt bv;
    std::string description;
    bool covered; //goal reachable?

    explicit goalt(const goto_programt::instructiont &instruction)
    {
      description=id2string(instruction.location.get_comment());
      covered = false;
    }
  
    goalt()
    {
    }
  };

  // Collect _all_ goals in `goal_map'.
  // This maps claim IDs to 'goalt'
  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;
 
  virtual bool all_claims(const goto_functionst &goto_functions);

};

#endif
