/*******************************************************************\

Module: Field-insensitive, location-sensitive, over-approximative
        escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GLOBAL_MAY_ALIAS_H
#define CPROVER_GLOBAL_MAY_ALIAS_H

#include <util/numbering.h>
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
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const global_may_alias_domaint &b,
    locationt from,
    locationt to);
    
  void make_bottom()
  {
    aliases.clear();
  }
  
  void make_top()
  {
    aliases.clear();
  }
  
  typedef union_find<irep_idt> aliasest;
  aliasest aliases;
  
protected:  
  void assign_lhs_aliases(const exprt &, const std::set<irep_idt> &);
  void get_rhs_aliases(const exprt &, std::set<irep_idt> &);
  void get_rhs_aliases_address_of(const exprt &, std::set<irep_idt> &);
};

class global_may_alias_analysist:public ait<global_may_alias_domaint> 
{
protected:
  virtual void initialize(const goto_functionst &_goto_functions,
    const namespacet &ns)
  {
  }
};

#endif
