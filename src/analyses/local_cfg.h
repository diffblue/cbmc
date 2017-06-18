/*******************************************************************\

Module: CFG for One Function

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CFG for One Function

#ifndef CPROVER_ANALYSES_LOCAL_CFG_H
#define CPROVER_ANALYSES_LOCAL_CFG_H

#include <util/numbering.h>

#include <goto-programs/goto_functions.h>

class local_cfgt
{
public:
  using node_nrt = std::size_t;
  using successorst = std::vector<node_nrt>;

  class nodet
  {
  public:
    goto_programt::const_targett t;
    successorst successors;
  };

  typedef std::map<goto_programt::const_targett, node_nrt> loc_mapt;
  loc_mapt loc_map;

  using nodest = std::vector<nodet>;
  nodest nodes;

  explicit local_cfgt(const goto_programt &_goto_program)
  {
    build(_goto_program);
  }

protected:
  void build(const goto_programt &goto_program);
};

#endif // CPROVER_ANALYSES_LOCAL_CFG_H
