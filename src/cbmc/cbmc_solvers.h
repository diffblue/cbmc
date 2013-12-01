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


/*******************************************************************\
Solver factory
\*******************************************************************/
 
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
    ns(_symbol_table)
  {
  }

  //The solver class (that takes care of allocated objects)
  class solvert {
    public:
      solvert(prop_convt* _prop_conv) {
        assert(_prop_conv!=NULL);
        prop_conv_ptr = _prop_conv;
      }
      ~solvert() {
        assert(prop_conv_ptr!=NULL);
        delete prop_conv_ptr;
      }

      //use this to get the prop_conv
      prop_convt& prop_conv() const { 
        assert(prop_conv_ptr!=NULL);
        return *prop_conv_ptr;
      }
    protected:
      prop_convt* prop_conv_ptr;
  };

  //returns a solvert object
  virtual std::auto_ptr<solvert> get_solver() {
    solvert* solver;
    if(options.get_bool_option("boolector")) solver = get_boolector();
    else if(options.get_bool_option("dimacs")) solver = get_dimacs();
    else if(options.get_bool_option("mathsat")) solver = get_mathsat();
    else if(options.get_bool_option("cvc")) solver = get_cvc();
    else if(options.get_bool_option("opensmt")) solver = get_opensmt();
    else if(options.get_bool_option("refine")) solver = get_bv_refinement();
    else if(options.get_bool_option("smt1")) 
	    // this is the 'default' smt1 solver
      solver = get_smt1(smt1_dect::BOOLECTOR);
    else if(options.get_bool_option("smt2"))
	    // this is the 'default' smt2 solver
      solver = get_smt2(smt2_dect::MATHSAT);
    else if(options.get_bool_option("yices"))
      solver = get_yices();
    else if(options.get_bool_option("z3"))
      solver = get_z3();
    else solver = get_default();
    return std::auto_ptr<solvert>(solver); 
  }

  virtual ~cbmc_solverst() { 
  }

protected:
  const optionst &options;
  const symbol_tablet &symbol_table;
  namespacet ns;

  solvert* get_default();
  solvert* get_dimacs();
  solvert* get_bv_refinement();
  solvert* get_smt1(smt1_dect::solvert solver);
  solvert* get_cvc();
  solvert* get_yices();
  solvert* get_smt2(smt2_dect::solvert solver);
  solvert* get_boolector();
  solvert* get_mathsat();
  solvert* get_opensmt();
  solvert* get_z3(); 

  //consistency checks during solver creation
  void no_beautification();
  void no_incremental_check();

};

#endif
