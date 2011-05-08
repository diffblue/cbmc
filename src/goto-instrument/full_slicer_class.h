/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_FULL_SLICER_CLASS_H
#define CPROVER_GOTO_PROGRAM_FULL_SLICER_CLASS_H

#include <stack>

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include "object_id.h"

/*******************************************************************\

   Class: full_slicert

 Purpose:

\*******************************************************************/

class full_slicert
{
public:
  void operator()(goto_functionst &goto_functions)
  {
    slice(goto_functions);
  }

protected:
  struct cfg_nodet
  {
    cfg_nodet():node_required(false)
    {
    }

    bool node_required;
    object_id_sett required_objects;
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::stack<cfgt::iterator> queuet;

  void fixedpoint();
  void slice(goto_functionst &goto_functions);
  object_id_sett transform(cfgt::iterator);
};

#endif
