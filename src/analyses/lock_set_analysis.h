/*******************************************************************\

Module: Lockset Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOCK_SET_H
#define CPROVER_POINTER_ANALYSIS_LOCK_SET_H

#include <analyses/ai.h>

#include <pointer-analysis/value_set_domain.h>
#include <pointer-analysis/value_sets.h>
#include <pointer-analysis/value_set_analysis.h>

class lock_set_domaint : public ai_domain_baset
{
public:
  typedef value_sett::object_mapt object_mapt;
  lock_set_domaint()
    : ai_domain_baset()
  {
    object_map.write().use_top = true;
  } 
  
  object_mapt object_map;

  value_set_analysist *value_set_analysis;

  inline bool merge(const lock_set_domaint &other, 
		    locationt from, locationt to)
  {
    return value_sett::make_union(object_map, other.object_map);
  }

  bool merge_shared(
    const lock_set_domaint &other,
    locationt from, locationt to,
    const namespacet &ns)
  {
    return value_sett::make_union(object_map, other.object_map);
  }

  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    ai_baset &ai,
    const namespacet &ns);

  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns)
  {
    (*value_set_analysis)[l].value_set.get_value_set(expr, dest, ns);
  }

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const
  {
    value_sett::output(ns, out, object_map);
  }

  // interface value_sets
  virtual const value_sett& get_value_set(
    locationt l)
  {
    return (*value_set_analysis)[l].value_set;
  }

  //TODO: this should go away in future
  static void clean_update(const object_mapt &new_objects, 
			   object_mapt &lock_objects);

};


class xmlt;

class lock_set_analysist:
  public ait<lock_set_domaint>
{
public:
  lock_set_analysist(value_set_analysist &_value_set_analysis):
    ait<lock_set_domaint>(),
    value_set_analysis(_value_set_analysis)
   {
   }

  typedef ait<lock_set_domaint> baset;

  // overloading
  virtual void initialize(const goto_programt &goto_program,
			  const namespacet &ns);

  virtual void convert(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    xmlt &dest);

  virtual void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    xmlt &dest);

  void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const;

  static std::string lock_function;
  static std::string unlock_function;

  value_set_analysist &value_set_analysis;
};

#endif
