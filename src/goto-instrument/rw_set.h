/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_RW_SET
#define CPROVER_GOTO_PROGRAMS_RW_SET

#include <iosfwd>
#include <vector>
#include <set>

#include <util/hash_cont.h>
#include <util/guard.h>
#include <util/std_code.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_sets.h>

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

// a container for read/write sets

class rw_set_baset
{
public:
  rw_set_baset(const namespacet &_ns)
    :ns(_ns)
  {
  }

  ~rw_set_baset() {}
 
  struct entryt
  {
    symbol_exprt symbol_expr;
    irep_idt object;
    exprt guard;
    
    entryt():guard(true_exprt())
    {
    }
  };
  
  typedef hash_map_cont<irep_idt, entryt, irep_id_hash> entriest;
  entriest r_entries, w_entries;
 
  void swap(rw_set_baset &other)
  {
    std::swap(other.r_entries, r_entries);
    std::swap(other.w_entries, w_entries);
  }
  
  inline rw_set_baset &operator += (const rw_set_baset &other)
  {
    r_entries.insert(other.r_entries.begin(), other.r_entries.end());
    w_entries.insert(other.w_entries.begin(), other.w_entries.end());
    return *this;
  }
  
  inline bool empty() const
  {	
    return r_entries.empty() && w_entries.empty();
  }
  
  inline bool has_w_entry(irep_idt object) const
  {
    return w_entries.find(object)!=w_entries.end();
  }
  
  inline bool has_r_entry(irep_idt object) const
  {
    return r_entries.find(object)!=r_entries.end();
  }
  
  void output(std::ostream &out) const;
  
protected:
  virtual void track_deref(const entryt& entry, bool read) {}
  virtual void set_track_deref() {}
  virtual void reset_track_deref() {}

  const namespacet &ns;
};

extern inline std::ostream & operator << (
  std::ostream &out, const rw_set_baset &rw_set)
{
  rw_set.output(out);
  return out;
}

#define forall_rw_set_r_entries(it, rw_set) \
  for(rw_set_baset::entriest::const_iterator it=(rw_set).r_entries.begin(); \
      it!=(rw_set).r_entries.end(); it++)
      
#define forall_rw_set_w_entries(it, rw_set) \
  for(rw_set_baset::entriest::const_iterator it=(rw_set).w_entries.begin(); \
      it!=(rw_set).w_entries.end(); it++)
      
// a producer of read/write sets

class _rw_set_loct:public rw_set_baset
{
public:
  inline _rw_set_loct(const namespacet &_ns,
                     value_setst &_value_sets,
                     goto_programt::const_targett _target
#ifdef LOCAL_MAY
                     , local_may_aliast &may
#endif
  ):
    rw_set_baset(_ns),
    value_sets(_value_sets),
    target(_target)
#ifdef LOCAL_MAY
    , local_may(may)
#endif
  {
  }

  ~_rw_set_loct() {}
  
protected:
  value_setst &value_sets;
  const goto_programt::const_targett target;

#ifdef LOCAL_MAY
  local_may_aliast& local_may;
#endif

  inline void read(const exprt &expr)
  {
    read_write_rec(expr, true, false, "", guardt());
  }
  
  inline void read(const exprt &expr, const guardt &guard)
  {
    read_write_rec(expr, true, false, "", guard);
  }
  
  inline void write(const exprt &expr)
  {
    read_write_rec(expr, false, true, "", guardt());
  }
  
  void compute();
  
  void assign(const exprt &lhs, const exprt &rhs);

  void read_write_rec(
    const exprt &expr,
    bool r, bool w,
    const std::string &suffix,
    const guardt &guard);
};

class rw_set_loct:public _rw_set_loct
{
public:
  inline rw_set_loct(const namespacet &_ns,
                     value_setst &_value_sets,
                     goto_programt::const_targett _target
#ifdef LOCAL_MAY
                     , local_may_aliast &may
#endif
  ):
    _rw_set_loct(_ns, _value_sets, _target
#ifdef LOCAL_MAY
      , may
#endif
   )
  {
    compute();
  }

  ~rw_set_loct() {}
};

// another producer, this time for entire functions

class rw_set_functiont:public rw_set_baset
{
public:
  rw_set_functiont(
    value_setst &_value_sets,
    const namespacet &_ns,
    const goto_functionst &_goto_functions,
    const exprt &function):
    rw_set_baset(_ns),
    value_sets(_value_sets),
    goto_functions(_goto_functions)
  {
    compute_rec(function);
  }

  ~rw_set_functiont() {}
  
protected:
  value_setst &value_sets;
  const goto_functionst &goto_functions;

  void compute_rec(const exprt &function);
};

/* rw_set_loc keeping track of the dereference path */

class rw_set_with_trackt:public _rw_set_loct
{
public:
  // NOTE: combine this with entriest to avoid double copy
  /* keeps track of who is dereferenced from who. 
     E.g., y=&z; x=*y;
     reads(x=*y;)={y,z} 
     dereferenced_from={z|->y} */
  std::map<const irep_idt, const irep_idt> dereferenced_from;

  /* is var a read or write */
  std::set<irep_idt> set_reads;

  inline rw_set_with_trackt(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target
#ifdef LOCAL_MAY
    , local_may_aliast& may
#endif
  ) : _rw_set_loct(_ns, _value_sets, _target
#ifdef LOCAL_MAY
      ,  may
#endif
      ), dereferencing(false)
  {
    compute();
  }

  ~rw_set_with_trackt() {}

protected:
  /* flag and variable in the expression, from which we dereference */
  bool dereferencing;
  std::vector<entryt> dereferenced;

  void track_deref(const entryt& entry, bool read) {
    if(dereferencing && dereferenced.size()==0)
    {
      dereferenced.insert(dereferenced.begin(), entry);
      if(read)
        set_reads.insert(entry.object);
    }
    else if(dereferencing && dereferenced.size()>0)
      dereferenced_from.insert(std::make_pair(entry.object,
        dereferenced.front().object));
  }

  void set_track_deref() {
    dereferencing=true;
  }
  
  void reset_track_deref() {
    dereferencing=false;
    dereferenced.clear();
  }
};

#endif
