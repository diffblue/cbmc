/*******************************************************************\

Module: Pretty name generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_PRETTY_NAMES_H
#define CPROVER_CBMC_PRETTY_NAMES_H

// THIS FILE WILL GO AWAY

#include <set>
#include <map>

#include <namespace.h>

class pretty_namest
{
 public:
  typedef std::set<irep_idt> symbolst;
  typedef std::map<irep_idt, irep_idt> pretty_mapt;
  
  pretty_mapt pretty_map;

  void get_pretty_names(const symbolst &symbols,
                        const namespacet &ns);
  
  const irep_idt &pretty_name(const irep_idt &identifier) const;
};

#endif
