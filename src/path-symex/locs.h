/*******************************************************************\

Module: CFG made of Program Locations, built from goto_functionst

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_LOCS_H
#define CPROVER_PATH_SYMEX_LOCS_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include "loc_ref.h"

struct loct
{
public:
  loct(goto_programt::const_targett _target,
       const irep_idt &_function):
       target(_target),
       function(_function)
  {
  }
  
  goto_programt::const_targett target;
  irep_idt function;
  
  typedef std::vector<loc_reft> targetst;
  targetst targets;
};

class locst
{  
public:
  typedef std::vector<loct> loc_vectort;
  loc_vectort loc_vector;
  loc_reft entry_loc;
  
  typedef std::pair<loc_reft, code_typet> function_entryt;
  typedef std::map<irep_idt, function_entryt> function_mapt;
  function_mapt function_map;
  
  locst(const namespacet &_ns);
  void build(const goto_functionst &goto_functions);
  void output(std::ostream &out) const;
  
  inline loct &operator[] (loc_reft l)
  {
    assert(l.loc_number>=0 && l.loc_number < loc_vector.size());
    return loc_vector[l.loc_number];
  }
  
  inline const loct &operator[] (loc_reft l) const
  {
    assert(l.loc_number>=0 && l.loc_number < loc_vector.size());
    return loc_vector[l.loc_number];
  }
  
  inline loc_reft last_loc() const
  {
    loc_reft tmp;
    tmp.loc_number=loc_vector.size();
    return tmp;
  }
  
protected:
  const namespacet &ns;
};

#define forall_locs(it, locs) \
  for(locst::loc_vectort::const_iterator it=(locs).loc_vector.begin(); \
      it!=(locs).loc_vector.end(); it++)

#define Forall_locs(it, locs) \
  for(exprt::operandst::iterator it=(expr).loc_vector.begin(); \
      it!=(locs).loc_vector.end(); it++)

#endif
