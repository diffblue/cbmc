/*******************************************************************\

Module: Lock Set Analysis (context-sensitive)

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOCK_SET_ANALYSIS_CS_H
#define CPROVER_POINTER_ANALYSIS_LOCK_SET_ANALYSIS_CS_H

#include <analyses/ai_cs.h>
#include <pointer-analysis/value_set_analysis_cs.h>
#include <pointer-analysis/value_sets_cs.h>
#include <util/misc_utils.h>

class xmlt;

// abstract base class
class lock_set_domain_base_cst:public ai_cs_domain_baset
{
public:
  lock_set_domain_base_cst() : value_set_analysis_cs(NULL)
  {
    assert(false);
  }

  lock_set_domain_base_cst(const value_set_analysis_cst &vsa)
  : value_set_analysis_cs(&vsa)
  {
  }

  typedef ai_cs_baset::placet placet;
  typedef std::set<placet> placest;
  typedef std::map<unsigned, placest> places_mapt;

  typedef value_sett::objectt objectt;
  typedef value_sett::object_mapt object_mapt;
  typedef value_sett::object_map_dt object_map_dt;

  // needs to be a pointer (not a reference), as we do not set its value when
  // the default constructor is called
  const value_set_analysis_cst *value_set_analysis_cs;

  object_mapt object_map;
  places_mapt places_map;

  bool valid_maps() const;

  bool has_top(const object_mapt &object_map) const;

  bool has_nonempty_intersection(const object_mapt &other) const;

  void get_value_set(
    const ai_cs_stackt &stack,
    locationt l,
    const exprt &arg,
    const namespacet &ns,
    object_mapt &object_map) const; // result

  bool merge_places(const places_mapt &other);

  bool merge_values(const object_mapt &other);

  bool intersect_values(const object_mapt &other);

  bool subtract_values(const object_mapt &other);

  virtual bool merge(
    const lock_set_domain_base_cst &other,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack)=0;

  virtual bool merge_shared(
    const lock_set_domain_base_cst &other,
    locationt from, locationt to,
    const namespacet &ns)
  {
    return false;
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns)=0;

  virtual void output(
    std::ostream &out,
    const ai_cs_baset &ai,
    const namespacet &ns) const;

  virtual void make_bottom()
  {
  }

  virtual void make_top()
  {
  }
};


// locks that may be held
class may_lock_set_domain_cst:public lock_set_domain_base_cst
{
public:
  static unsigned num_lock_case1;
  static unsigned num_lock_case2;

  may_lock_set_domain_cst()
  {
    assert(false);
  }

  may_lock_set_domain_cst(const value_set_analysis_cst &vsa)
  : lock_set_domain_base_cst(vsa)
  {}

  virtual bool merge(
    const lock_set_domain_base_cst &other,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack);

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns);

  static void output_stats(
    std::ostream &out)
  {
    out << "*** Statistics" << std::endl;
    out << "May-lockset lock case1: " << num_lock_case1 << "\n";
    out << "May-lockset lock case2: " << num_lock_case2 << "\n";
  }
};


// locks that must be held
class must_lock_set_domain_cst:public lock_set_domain_base_cst
{
public:
  bool all;

  static unsigned num_all_case;
  static unsigned num_lock_case1;
  static unsigned num_lock_case2;

  must_lock_set_domain_cst() : all(true)
  {
    assert(false);
  }

  must_lock_set_domain_cst(const value_set_analysis_cst &vsa)
  : lock_set_domain_base_cst(vsa), all(true)
  {}

  virtual bool merge(
    const lock_set_domain_base_cst &other,
    locationt from,
    locationt to,
    const ai_cs_stackt &stack);

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns);

  virtual void make_top()
  {
    all=false;
  }

  static void output_stats(
    std::ostream &out)
  {
    out << "*** Statistics" << std::endl;
#if 0
    out << "Must-lockset all case: " << num_all_case << "\n";
#endif
    out << "Must-lockset lock case1: " << num_lock_case1 << "\n";
    out << "Must-lockset lock case2: " << num_lock_case2 << "\n";
  }
};


template<typename lock_set_domainT>
class lock_set_analysis_cst:public ai_cst<lock_set_domainT>
{
public:
  lock_set_analysis_cst(
    in_loopt &in_loop,
    value_set_analysis_cst &_value_set_analysis)
    :
    ai_cst<lock_set_domainT>(in_loop),
    value_set_analysis(_value_set_analysis)
  {
  }

  lock_set_analysis_cst(
    in_loopt &in_loop,
    value_set_analysis_cst &_value_set_analysis,
    stack_numberingt &stack_numbering)
    :
    ai_cst<lock_set_domainT>(in_loop, stack_numbering),
    value_set_analysis(_value_set_analysis)
  {
  }

  // template superclass not considered for name resolution
  typedef ai_cst<lock_set_domainT> baset;
  typedef typename baset::statet statet;
  typedef typename baset::state_mapt state_mapt;
  typedef typename baset::location_mapt location_mapt;
  typedef typename baset::locationt locationt;
  using baset::state_map;
  using baset::get_stack_number;

  // override as we need to call a non-default constructor
  virtual statet &get_state(const ai_cs_stackt &stack, locationt l)
  {
    unsigned sn=get_stack_number(stack);
    location_mapt &lm=state_map[sn];

    typename location_mapt::iterator it=lm.find(l);
    if(it!=lm.end())
      return it->second;

    lock_set_domainT lsd(value_set_analysis);

    std::pair<typename location_mapt::iterator, bool> r
      =lm.insert(std::make_pair(l, lsd));
    assert(r.second);

    return r.first->second;
  }

  // override as we need to call a non-default constructor
  virtual const statet &get_const_state(const ai_cs_stackt &stack, locationt l)
  {
    return get_state(stack, l);
  }

  void output_stats(std::ostream &out)
  {
    lock_set_domainT::output_stats(out);
  }

  const value_set_analysis_cst &value_set_analysis;
protected:

private:
  // to enforce that lock_set_domainT is derived from lock_set_domain_base_cst
  void dummy(const lock_set_domainT &s)
  {
    const lock_set_domain_base_cst &x=s; (void)x;
  }
};

typedef lock_set_analysis_cst<may_lock_set_domain_cst>
  may_lock_set_analysis_cst;

typedef lock_set_analysis_cst<must_lock_set_domain_cst>
  must_lock_set_analysis_cst;

void collect_lock_operations(
  const goto_functionst &goto_functions,
  std::vector<exprt> &exprs,
  std::set<goto_programt::const_targett> &lock_locations);

#endif
