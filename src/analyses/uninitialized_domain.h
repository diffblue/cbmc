/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#include "static_analysis.h"

class uninitialized_domaint:public domain_baset
{
public:
  // locals that are not initialized
  typedef std::set<irep_idt> uninitializedt;
  uninitializedt uninitialized;

  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to);

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;
  
  // returns true iff there is s.th. new
  bool merge(const uninitialized_domaint &other);
  
protected:
  void assign(const exprt &lhs);
};

typedef static_analysist<uninitialized_domaint>
  uninitialized_analysist;

