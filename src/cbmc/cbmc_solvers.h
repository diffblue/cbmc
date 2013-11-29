/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_SOLVERS_H
#define CPROVER_CBMC_SOLVERS_H

#include <list>
#include <map>

#include <util/hash_cont.h>
#include <util/options.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/prop/aig_prop.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>
#include <langapi/language_ui.h>
#include <goto-symex/symex_target_equation.h>

#include "bv_cbmc.h"


class cbmc_solverst:public messaget
{
public:
  cbmc_solverst(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    messaget(_message_handler),
    options(_options),
    symbol_table(_symbol_table),
    ns(_symbol_table),
    prop_conv(NULL),prop(NULL),aig(NULL)
  {
  }
 
  virtual prop_convt& get_solver() {
    if(options.get_bool_option("boolector")) prop_conv = get_boolector();
    else if(options.get_bool_option("dimacs")) prop_conv = get_dimacs();
    else if(options.get_bool_option("mathsat")) prop_conv = get_mathsat();
    else if(options.get_bool_option("cvc")) prop_conv = get_cvc();
    else if(options.get_bool_option("opensmt")) prop_conv = get_opensmt();
    else if(options.get_bool_option("refine")) prop_conv = get_bv_refinement();
    else if(options.get_bool_option("smt1")) 
	    // this is the 'default' smt1 solver
      prop_conv = get_smt1(smt1_dect::BOOLECTOR);
    else if(options.get_bool_option("smt2"))
	    // this is the 'default' smt2 solver
      prop_conv = get_smt2(smt2_dect::MATHSAT);
    else if(options.get_bool_option("yices"))
      prop_conv = get_yices();
    else if(options.get_bool_option("z3"))
      prop_conv = get_z3();
    else prop_conv = get_default();
    return *prop_conv; 
  }

  virtual ~cbmc_solverst() { 
    if(aig!=NULL) delete aig;
    if(prop!=NULL) delete prop;
    if(prop_conv!=NULL) delete prop_conv;
  }

protected:
  const optionst &options;
  const symbol_tablet &symbol_table;
  namespacet ns;

  //allocated objects
  prop_convt* prop_conv;
  propt* prop;
  aigt* aig;

  prop_convt* get_default();
  prop_convt* get_dimacs();
  prop_convt* get_bv_refinement();
  prop_convt* get_smt1(smt1_dect::solvert solver);
  prop_convt* get_cvc();
  prop_convt* get_yices();
  prop_convt* get_smt2(smt2_dect::solvert solver);
  prop_convt* get_boolector();
  prop_convt* get_mathsat();
  prop_convt* get_opensmt();
  prop_convt* get_z3(); 

  void no_beautification();
  void no_incremental_check();

};

#endif
