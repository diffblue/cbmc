/*******************************************************************\

Module: CFG for One Function

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_CFG_H
#define CPROVER_LOCAL_CFG_H

#include <util/numbering.h>

#include <goto-programs/goto_functions.h>

/*******************************************************************\

   Class: local_cfgt
   
 Purpose:

\*******************************************************************/

class local_cfgt
{
public:
  typedef std::vector<unsigned> successorst;

  class loct
  {
  public:
    goto_programt::const_targett t;
    successorst successors;
  };

  typedef std::map<goto_programt::const_targett, unsigned> loc_mapt;
  loc_mapt loc_map;
  
  typedef std::vector<loct> locst;
  locst locs;
  
  inline explicit local_cfgt(const goto_programt &_goto_program)
  {
    build(_goto_program);
  }

protected:  
  void build(const goto_programt &goto_program);
};

#endif
