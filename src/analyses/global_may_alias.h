/*******************************************************************\

Module: Field-insensitive, location-sensitive, over-approximative
        escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H
#define CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H

#include <util/numbering.h>
#include <util/threeval.h>
#include <util/union_find.h>

#include "ai.h"

/*******************************************************************\

   Class: global_may_alias_domaint

 Purpose:

\*******************************************************************/

class global_may_alias_analysist;

class global_may_alias_domaint:public ai_domain_baset
{
public:
  global_may_alias_domaint():has_values(false)
  {
  }

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const final;

  bool merge(
    const global_may_alias_domaint &b,
    locationt from,
    locationt to);

  void make_bottom() final
  {
    aliases.clear();
    has_values=tvt(false);
  }

  void make_top() final
  {
    aliases.clear();
    has_values=tvt(true);
  }

  void make_entry() final
  {
    make_top();
  }

  typedef union_find<irep_idt> aliasest;
  aliasest aliases;

private:
  tvt has_values;

  void assign_lhs_aliases(const exprt &, const std::set<irep_idt> &);
  void get_rhs_aliases(const exprt &, std::set<irep_idt> &);
  void get_rhs_aliases_address_of(const exprt &, std::set<irep_idt> &);
};

class global_may_alias_analysist:public ait<global_may_alias_domaint>
{
protected:
  virtual void initialize(const goto_functionst &_goto_functions)
  {
  }
};

#endif // CPROVER_ANALYSES_GLOBAL_MAY_ALIAS_H
