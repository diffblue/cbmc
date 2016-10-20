/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/prop/cover_goals.h>

#include "bmc.h"

/*******************************************************************\

   Class: bmc_all_propertiest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class bmc_all_propertiest:
  public cover_goalst::observert,
  public messaget
{
public:
  bmc_all_propertiest(
    const goto_functionst &_goto_functions,
    prop_convt &_solver,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_solver), bmc(_bmc)
  {
  }

  safety_checkert::resultt operator()();

  virtual void goal_covered(const cover_goalst::goalt &);

  struct goalt
  {
    // a property holds if all instances of it are true
    typedef std::vector<symex_target_equationt::SSA_stepst::iterator> instancest;
    instancest instances;
    std::string description;
    
    // if failed, we compute a goto_trace for the first failing instance
    enum statust { UNKNOWN, FAILURE, SUCCESS, ERROR } status;
    goto_tracet goto_trace;
    
    std::string status_string() const
    {
      switch(status)
      {
      case UNKNOWN: return "UNKNOWN";
      case FAILURE: return "FAILURE";
      case SUCCESS: return "SUCCESS";
      case ERROR: return "ERROR";
      }

      // make some poor compilers happy
      assert(false);
      return "";
    }
    
    explicit goalt(
      const goto_programt::instructiont &instruction):
      status(statust::UNKNOWN)
    {
      description=id2string(instruction.source_location.get_comment());
    }
    
    goalt():status(statust::UNKNOWN)
    {
    }
    
    exprt as_expr() const
    {
      std::vector<exprt> tmp;
      for(instancest::const_iterator
          it=instances.begin();
          it!=instances.end();
          it++)
        tmp.push_back(literal_exprt((*it)->cond_literal));
      return conjunction(tmp);
    }
  };

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

protected:
  const goto_functionst &goto_functions;
  prop_convt &solver;
  bmct &bmc;

  virtual void report(const cover_goalst &cover_goals);
  virtual void do_before_solving() {}
};

