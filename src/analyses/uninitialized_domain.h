/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#ifndef CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H
#define CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H

#include "ai.h"

class uninitialized_domaint:public ai_domain_baset
{
public:
  // locals that are not initialized
  typedef std::set<irep_idt> uninitializedt;
  uninitializedt uninitialized;

  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  // returns true iff there is s.th. new
  bool merge(
    const uninitialized_domaint &other,
    locationt from,
    locationt to);

protected:
  void assign(const exprt &lhs);
};

typedef ait<uninitialized_domaint>
  uninitialized_analysist;

#endif // CPROVER_ANALYSES_UNINITIALIZED_DOMAIN_H
