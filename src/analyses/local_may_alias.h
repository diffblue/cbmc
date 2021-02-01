/*******************************************************************\

Module: Field-insensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive may-alias analysis

#ifndef CPROVER_ANALYSES_LOCAL_MAY_ALIAS_H
#define CPROVER_ANALYSES_LOCAL_MAY_ALIAS_H

#include <memory>
#include <stack>

#include <util/union_find.h>
#include <util/make_unique.h>

#include "locals.h"
#include "dirty.h"
#include "local_cfg.h"

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

  // given a pointer, returns possible aliases
  std::set<exprt> get(
    const goto_programt::const_targett t,
    const exprt &src) const;

  // returns 'true' when pointers src1 and src2 may be aliases
  bool aliases(
    const goto_programt::const_targett t,
    const exprt &src1, const exprt &src2) const;

protected:
  void build(const goto_functiont &goto_function);

  typedef std::stack<local_cfgt::node_nrt> work_queuet;

  mutable numberingt<exprt, irep_hash> objects;

  typedef unsigned_union_find alias_sett;

  // the information tracked per program location
  class loc_infot
  {
  public:
    alias_sett aliases;

    bool merge(const loc_infot &src);
  };

  typedef std::vector<loc_infot> loc_infost;
  loc_infost loc_infos;

  void assign_lhs(
    const exprt &lhs,
    const exprt &rhs,
    const loc_infot &loc_info_src,
    loc_infot &loc_info_dest);

  typedef std::set<unsigned> object_sett;

  void get_rec(
    object_sett &dest,
    const exprt &rhs,
    const loc_infot &loc_info_src) const;

  unsigned unknown_object;
};

class local_may_alias_factoryt
{
public:
  local_may_alias_factoryt():goto_functions(nullptr)
  {
  }

  void operator()(const goto_functionst &_goto_functions)
  {
    goto_functions=&_goto_functions;

    for(const auto &gf_entry : _goto_functions.function_map)
    {
      forall_goto_program_instructions(i_it, gf_entry.second.body)
        target_map[i_it] = gf_entry.first;
    }
  }

  local_may_aliast &operator()(const irep_idt &fkt)
  {
    PRECONDITION(goto_functions!=nullptr);
    fkt_mapt::iterator f_it=fkt_map.find(fkt);
    if(f_it!=fkt_map.end())
      return *f_it->second;

    goto_functionst::function_mapt::const_iterator f_it2=
      goto_functions->function_map.find(fkt);
    assert(f_it2!=goto_functions->function_map.end());
    return *(fkt_map[fkt]=util_make_unique<local_may_aliast>(f_it2->second));
  }

  local_may_aliast &operator()(goto_programt::const_targett t)
  {
    target_mapt::const_iterator t_it=
      target_map.find(t);
    assert(t_it!=target_map.end());
    return operator()(t_it->second);
  }

  std::set<exprt> get(
    const goto_programt::const_targett t,
    const exprt &src) const;

protected:
  const goto_functionst *goto_functions;
  typedef std::map<irep_idt, std::unique_ptr<local_may_aliast> > fkt_mapt;
  fkt_mapt fkt_map;

  typedef std::map<goto_programt::const_targett, irep_idt > target_mapt;
  target_mapt target_map;
};

#endif // CPROVER_ANALYSES_LOCAL_MAY_ALIAS_H
