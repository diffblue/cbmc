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
  typedef std::size_t node_nrt;
  typedef std::vector<node_nrt> successorst;

  class nodet
  {
  public:
    goto_programt::const_targett t;
    successorst successors;
  };

  typedef std::map<goto_programt::const_targett, node_nrt> loc_mapt;
  loc_mapt loc_map;
  
  typedef std::vector<nodet> nodest;
  nodest nodes;
  
  inline explicit local_cfgt(const goto_programt &_goto_program)
  {
    build(_goto_program);
  }

protected:  
  void build(const goto_programt &goto_program);
};

#endif
