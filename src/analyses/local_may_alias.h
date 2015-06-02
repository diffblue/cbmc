/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_MAY_ALIAS_H
#define CPROVER_LOCAL_MAY_ALIAS_H

#include <stack>

#include "locals.h"
#include "dirty.h"
#include "local_cfg.h"

/*******************************************************************\

   Class: local_may_aliast
   
 Purpose:

\*******************************************************************/

class local_may_aliast
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  
  explicit local_may_aliast(
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
  local_cfgt cfg;

  std::set<exprt> get(
    const goto_programt::const_targett t,
    const exprt &src) const;

  bool aliases(
    const goto_programt::const_targett t,
    const exprt &src1, const exprt &src2) const;
    
protected:
  void build(const goto_functiont &goto_function);

  typedef std::stack<local_cfgt::node_nrt> work_queuet;

  // the following may eventually get merged  
  mutable numbering<irep_idt> pointers;
  mutable numbering<exprt> objects;
  
  // The following struct describes what a pointer
  // may point to
  struct destt
  {
  public:
    inline destt()
    {
    }
  
    std::set<unsigned> objects;
    
    bool merge(const destt &);

    inline void clear()
    { 
      objects.clear();
    }
  };
  
  // pointers -> destt
  typedef std::map<unsigned, destt> points_tot;

  // the information tracked per program location  
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
    destt &dest,
    const exprt &rhs,
    const loc_infot &loc_info_src) const;
    
  bool is_tracked(const irep_idt &identifier) const;
  
  unsigned unknown_object;
  std::set<exprt> empty_set;
};

#endif
