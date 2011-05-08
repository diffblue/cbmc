/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>

#include <hash_cont.h>
#include <options.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>
#include <langapi/language_ui.h>
#include <goto-symex/symex_target_equation.h>

#include "symex_bmc.h"

class bmc_baset:public messaget
{
public:
  bmc_baset(
    const namespacet &_ns,
    symex_bmct &_symex,
    symex_target_equationt &_equation,
    message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_ns),
    symex(_symex),
    equation(_equation),
    ui(ui_message_handlert::PLAIN)
  {
  }
 
  optionst options;
  
  virtual bool run(const goto_functionst &goto_functions);
  virtual ~bmc_baset() { }

  // additional stuff   
  expr_listt bmc_constraints;  
  
  friend class cbmc_satt;
  friend class hw_cbmc_satt;
  friend class counterexample_beautification_greedyt;
  
  void set_ui(language_uit::uit _ui) { ui=_ui; }
  
protected:
  const namespacet &ns;
  symex_bmct &symex;
  symex_target_equationt &equation;
 
  // use gui format
  language_uit::uit ui;
  
  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);
    
  virtual bool decide(prop_convt &prop_conv);
    
  // the solvers we have
  virtual bool decide_default();
  virtual bool decide_bv_refinement();
  virtual bool decide_cvc();
  virtual bool decide_yices();
  virtual bool decide_smt1(smt1_dect::solvert solver);
  virtual bool decide_smt2(smt2_dect::solvert solver);
  virtual bool decide_boolector();
  virtual bool decide_z3();
  virtual void smt1_convert(std::ostream &out);
  virtual void smt2_convert(std::ostream &out);
  virtual bool write_dimacs();
  virtual bool write_dimacs(std::ostream &out);
  
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
};

class bmct:public bmc_baset
{
public:
  bmct(
    const contextt &_context,
    message_handlert &_message_handler):
    bmc_baset(_ns, _symex, _equation, _message_handler),
    _ns(_context, new_context),
    _equation(ns),
    _symex(ns, new_context, _equation)
  {
  }
 
protected:
  contextt new_context;
  namespacet _ns;
  symex_target_equationt _equation;
  symex_bmct _symex;
};

#endif
