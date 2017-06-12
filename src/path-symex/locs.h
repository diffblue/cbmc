/*******************************************************************\

Module: CFG made of Program Locations, built from goto_functionst

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CFG made of Program Locations, built from goto_functionst

#ifndef CPROVER_PATH_SYMEX_LOCS_H
#define CPROVER_PATH_SYMEX_LOCS_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include "loc_ref.h"

struct loct
{
public:
  loct(
    goto_programt::const_targett _target,
    const irep_idt &_function):
    target(_target),
    function(_function)
  {
  }

  goto_programt::const_targett target;
  irep_idt function;

  // we only support a single branch target
  loc_reft branch_target;
};

class locst
{
public:
  typedef std::vector<loct> loc_vectort;
  loc_vectort loc_vector;
  loc_reft entry_loc;

  class function_entryt
  {
  public:
    loc_reft first_loc;
    code_typet type;
  };

  typedef std::map<irep_idt, function_entryt> function_mapt;
  function_mapt function_map;

  explicit locst(const namespacet &_ns);
  void build(const goto_functionst &goto_functions);
  void output(std::ostream &out) const;

  loct &operator[] (loc_reft l)
  {
    assert(l.loc_number<loc_vector.size());
    return loc_vector[l.loc_number];
  }

  const loct &operator[] (loc_reft l) const
  {
    assert(l.loc_number<loc_vector.size());
    return loc_vector[l.loc_number];
  }

  static inline loc_reft begin()
  {
    loc_reft tmp;
    tmp.loc_number=0;
    return tmp;
  }

  loc_reft end() const
  {
    loc_reft tmp;
    tmp.loc_number=loc_vector.size();
    return tmp;
  }

  std::size_t size() const
  {
    return loc_vector.size();
  }

protected:
  const namespacet &ns;
};

class target_to_loc_mapt
{
public:
  explicit target_to_loc_mapt(const locst &locs)
  {
    for(loc_reft it=locs.begin(); it!=locs.end(); ++it)
      map[locs[it].target]=it;
  }

  loc_reft operator[](const goto_programt::const_targett t) const
  {
    mapt::const_iterator it=map.find(t);
    assert(it!=map.end());
    return it->second;
  }

protected:
  typedef std::map<goto_programt::const_targett, loc_reft> mapt;
  mapt map;
};

#endif // CPROVER_PATH_SYMEX_LOCS_H
