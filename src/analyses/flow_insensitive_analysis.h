/*******************************************************************\

Module: Flow Insensitive Static Analysis

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ANALYSES_FLOW_INSENSITIVE_H_
#define CPROVER_ANALYSES_FLOW_INSENSITIVE_H_

#include <queue>
#include <map>
#include <iosfwd>

#include <goto-programs/goto_functions.h>

#include "ai.h"

class flow_insensitive_analysis_baset : public ai_baset
{
public:
  typedef ai_domain_baset statet;
  typedef goto_programt::const_targett locationt;

  flow_insensitive_analysis_baset()
  {
  }
  
  virtual ~flow_insensitive_analysis_baset()
  {
  }
  
  
  virtual statet &get_state(locationt)=0;
  virtual const statet &get_state() const=0;
    
protected:
  locationt entry_location;

  virtual void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const;
  
  virtual void entry_state(const goto_programt &);
  
};
  
// domainT is expected to be derived from ai_domain_baset
template<typename domainT>
class flow_insensitive_analysist : public flow_insensitive_analysis_baset
  {
public:
  // constructor
  flow_insensitive_analysist():flow_insensitive_analysis_baset()
  {
    state.make_bottom();
    top_state.make_top();
  }
  
  typedef goto_programt::const_targett locationt;
    
  virtual void clear()
    {
    state.clear();
    ai_baset::clear();
  }
  
  virtual statet &get_state() { return state; }
  virtual const statet &get_state() const { return state; }  
    
protected:
  domainT state; // one global state
  domainT top_state; // this should not be modified

  // this one creates states, if need be
  virtual statet &get_state(locationt l)
  {
    if(l == entry_location)
      return top_state;
    return state;
  }

  // this one just finds states
  virtual const statet &find_state(locationt l) const
  {
    if(l == entry_location)
      return top_state;
    return state;
  }
  
  virtual bool merge(const statet &src, locationt from, locationt to)
  {
    statet &dest=get_state();
    return static_cast<domainT &>(dest).merge(static_cast<const domainT &>(src), from, to);
  }

  virtual statet *make_temporary_state(const statet &s)
  {
    return new domainT(static_cast<const domainT &>(s));
  }

  virtual void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    ai_baset::sequential_fixedpoint(goto_functions, ns);
  }
  
private:  
  // to enforce that domainT is derived from ai_domain_baset
  void dummy(const domainT &s) { const statet &x=dummy1(s); (void)x; }
  
  // not implemented in sequential analyses
  virtual bool merge_shared(
    const statet &src,
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    const namespacet &ns)
  {
    throw "not implemented";
  }

};

template<typename domainT>
class concurrency_aware_flow_insensitive_analysist:public flow_insensitive_analysist<domainT>
{
public:
  typedef typename flow_insensitive_analysist<domainT>::statet statet;

  // constructor
  concurrency_aware_flow_insensitive_analysist():flow_insensitive_analysist<domainT>()
  {
  }

  virtual bool merge_shared(
    const statet &src,
    goto_programt::const_targett from,
    goto_programt::const_targett to,
    const namespacet &ns)
  {
    statet &dest=typename flow_insensitive_analysist<domainT>::get_state();
    return static_cast<domainT &>(dest).merge_shared(static_cast<const domainT &>(src), from, to, ns);
  }
  
protected:
  virtual void fixedpoint(
    const goto_functionst &goto_functions,
    const namespacet &ns)
  {
    this->concurrent_fixedpoint(goto_functions, ns);
  }
};

#endif /*CPROVER_ANALYSES_FLOW_INSENSITIV_H_*/
