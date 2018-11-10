/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_RW_SET_H
#define CPROVER_GOTO_INSTRUMENT_RW_SET_H

#include <iosfwd>
#include <vector>
#include <set>

#include <util/guard.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

class namespacet;
class value_setst;

// a container for read/write sets

class rw_set_baset
{
public:
  explicit rw_set_baset(const namespacet &_ns)
    :ns(_ns)
  {
  }

  virtual ~rw_set_baset() = default;

  struct entryt
  {
    symbol_exprt symbol_expr;
    irep_idt object;
    exprt guard;

    entryt():guard(true_exprt())
    {
    }
  };

  typedef std::unordered_map<irep_idt, entryt> entriest;
  entriest r_entries, w_entries;

  void swap(rw_set_baset &other)
  {
    std::swap(other.r_entries, r_entries);
    std::swap(other.w_entries, w_entries);
  }

  rw_set_baset &operator+=(const rw_set_baset &other)
  {
    r_entries.insert(other.r_entries.begin(), other.r_entries.end());
    w_entries.insert(other.w_entries.begin(), other.w_entries.end());
    return *this;
  }

  bool empty() const
  {
    return r_entries.empty() && w_entries.empty();
  }

  bool has_w_entry(irep_idt object) const
  {
    return w_entries.find(object)!=w_entries.end();
  }

  bool has_r_entry(irep_idt object) const
  {
    return r_entries.find(object)!=r_entries.end();
  }

  void output(std::ostream &out) const;

protected:
  virtual void track_deref(const entryt &, bool read)
  {
    (void)read; // unused parameter
  }
  virtual void set_track_deref() {}
  virtual void reset_track_deref() {}

  const namespacet &ns;
};

inline std::ostream &operator<<(
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
#ifdef LOCAL_MAY
  _rw_set_loct(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target,
    local_may_aliast &may):
    rw_set_baset(_ns),
    value_sets(_value_sets),
    target(_target),
    local_may(may)
#else
  _rw_set_loct(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target):
    rw_set_baset(_ns),
    value_sets(_value_sets),
    target(_target)
#endif
  {
  }

protected:
  value_setst &value_sets;
  const goto_programt::const_targett target;

#ifdef LOCAL_MAY
  local_may_aliast &local_may;
#endif

  void read(const exprt &expr)
  {
    read_write_rec(expr, true, false, "", guardt());
  }

  void read(const exprt &expr, const guardt &guard)
  {
    read_write_rec(expr, true, false, "", guard);
  }

  void write(const exprt &expr)
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
#ifdef LOCAL_MAY
  rw_set_loct(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target,
    local_may_aliast &may):
    _rw_set_loct(_ns, _value_sets, _target, may)
#else
  rw_set_loct(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target):
    _rw_set_loct(_ns, _value_sets, _target)
#endif
  {
    compute();
  }
};

// another producer, this time for entire functions

class rw_set_functiont:public rw_set_baset
{
public:
  rw_set_functiont(
    value_setst &_value_sets,
    const goto_modelt &_goto_model,
    const exprt &function):
    rw_set_baset(ns),
    ns(_goto_model.symbol_table),
    value_sets(_value_sets),
    goto_functions(_goto_model.goto_functions)
  {
    compute_rec(function);
  }

protected:
  const namespacet ns;
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

#ifdef LOCAL_MAY
  rw_set_with_trackt(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target,
    local_may_aliast &may):
    _rw_set_loct(_ns, _value_sets, _target, may),
    dereferencing(false)
#else
  rw_set_with_trackt(
    const namespacet &_ns,
    value_setst &_value_sets,
    goto_programt::const_targett _target):
    _rw_set_loct(_ns, _value_sets, _target),
    dereferencing(false)
#endif
  {
    compute();
  }

protected:
  /* flag and variable in the expression, from which we dereference */
  bool dereferencing;
  std::vector<entryt> dereferenced;

  void track_deref(const entryt &entry, bool read)
  {
    if(dereferencing && dereferenced.empty())
    {
      dereferenced.insert(dereferenced.begin(), entry);
      if(read)
        set_reads.insert(entry.object);
    }
    else if(dereferencing && !dereferenced.empty())
      dereferenced_from.insert(
        std::make_pair(entry.object, dereferenced.front().object));
  }

  void set_track_deref()
  {
    dereferencing=true;
  }

  void reset_track_deref()
  {
    dereferencing=false;
    dereferenced.clear();
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_RW_SET_H
