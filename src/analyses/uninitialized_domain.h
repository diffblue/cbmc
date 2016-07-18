/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

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
    const namespacet &ns,
    std::ostream &out) const;
  
  // returns true iff there is s.th. new
  bool merge(const uninitialized_domaint &other, 
	     locationt from, locationt to);
  
protected:
  void assign(const exprt &lhs);
};

typedef ait<uninitialized_domaint>
  uninitialized_analysist;

