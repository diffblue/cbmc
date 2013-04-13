/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_MAY_ALIAS_H
#define CPROVER_LOCAL_MAY_ALIAS_H

#include <ostream>
#include <stack>

#include <util/numbering.h>

#include <goto-programs/goto_functions.h>

#include "dirty.h"
#include "locals.h"

/*******************************************************************\

   Class: local_may_aliast
   
 Purpose:

\*******************************************************************/

class cfgt
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
  
  inline explicit cfgt(const goto_programt &_goto_program)
  {
    build(_goto_program);
  }

protected:  
  void build(const goto_programt &goto_program);
};

class local_may_aliast
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  
  local_may_aliast(
    const goto_functiont &_goto_function):
    dirty(_goto_function),
    locals(_goto_function),
    cfg(_goto_function.body)
  {
    build(_goto_function);
  }

  void output(
    std::ostream &out,
    const goto_functiont &goto_function,
    const namespacet &ns) const;
  
  dirtyt dirty;
  localst locals;
  cfgt cfg;

  std::set<exprt> get(
    const goto_programt::const_targett t,
    const exprt &src);

  bool aliases(
    const goto_programt::const_targett t,
    const exprt &src1, const exprt &src2);
  
protected:
  void build(const goto_functiont &goto_function);

  typedef std::stack<unsigned> work_queuet;
  
  numbering<irep_idt> pointers;
  numbering<exprt> objects;
  
  // pointers -> set of objects
  typedef std::map<unsigned, std::set<unsigned> > points_tot;
  
  class loc_infot
  {
  public:
    points_tot points_to;
    
    bool merge(const loc_infot &src);
  };

  typedef std::vector<loc_infot> loc_infost;
  loc_infost loc_infos;
  
  void assign_lhs(
    const exprt &lhs,
    const exprt &rhs,
    const loc_infot &loc_info_src,
    loc_infot &loc_info_dest);
    
  void get_rec(
    std::set<unsigned> &dest,
    const exprt &rhs,
    const loc_infot &loc_info_src);
    
  bool track(const irep_idt &identifier);
  
  unsigned unknown_object;
  std::set<exprt> empty_set;
};

#endif
