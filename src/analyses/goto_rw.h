/*******************************************************************\

Module:

Author: Daniel Kroening

Date: April 2010

\*******************************************************************/


#ifndef CPROVER_ANALYSES_GOTO_RW_H
#define CPROVER_ANALYSES_GOTO_RW_H

#include <iosfwd>
#include <limits>
#include <map>
#include <memory> // unique_ptr

#include <util/guard.h>

#include <goto-programs/goto_model.h>

#define forall_rw_range_set_r_objects(it, rw_set) \
  for(rw_range_sett::objectst::const_iterator it=(rw_set).get_r_set().begin(); \
      it!=(rw_set).get_r_set().end(); ++it)

#define forall_rw_range_set_w_objects(it, rw_set) \
  for(rw_range_sett::objectst::const_iterator it=(rw_set).get_w_set().begin(); \
      it!=(rw_set).get_w_set().end(); ++it)

class rw_range_sett;
class goto_modelt;

void goto_rw(
  const irep_idt &function,
  goto_programt::const_targett target,
  rw_range_sett &rw_set);

void goto_rw(
  const irep_idt &function,
  const goto_programt &,
  rw_range_sett &rw_set);

void goto_rw(const goto_functionst &,
             const irep_idt &function,
             rw_range_sett &rw_set);

class range_domain_baset
{
public:
  range_domain_baset()=default;

  range_domain_baset(const range_domain_baset &rhs)=delete;
  range_domain_baset &operator=(const range_domain_baset &rhs)=delete;

  range_domain_baset(range_domain_baset &&rhs)=delete;
  range_domain_baset &operator=(range_domain_baset &&rhs)=delete;

  virtual ~range_domain_baset();

  virtual void output(const namespacet &ns, std::ostream &out) const=0;
};

typedef int range_spect;

inline range_spect to_range_spect(const mp_integer &size)
{
  assert(size.is_long());
  mp_integer::llong_t ll=size.to_long();
  assert(ll<=std::numeric_limits<range_spect>::max());
  assert(ll>=std::numeric_limits<range_spect>::min());
  return (range_spect)ll;
}

// each element x represents a range of bits [x.first, x.second.first)
class range_domaint:public range_domain_baset
{
  typedef std::list<std::pair<range_spect, range_spect>> sub_typet;
  sub_typet data;

public:
  void output(const namespacet &ns, std::ostream &out) const override;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef sub_typet::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef sub_typet::const_iterator const_iterator;

  iterator begin() { return data.begin(); }
  const_iterator begin() const { return data.begin(); }
  const_iterator cbegin() const { return data.begin(); }

  iterator end() { return data.end(); }
  const_iterator end() const { return data.end(); }
  const_iterator cend() const { return data.end(); }

  void push_back(const sub_typet::value_type &v) { data.push_back(v); }
  void push_back(sub_typet::value_type &&v) { data.push_back(std::move(v)); }
};

class array_exprt;
class byte_extract_exprt;
class dereference_exprt;
class if_exprt;
class index_exprt;
class member_exprt;
class shift_exprt;
class struct_exprt;
class typecast_exprt;

class rw_range_sett
{
public:
  #ifdef USE_DSTRING
  typedef std::map<irep_idt, std::unique_ptr<range_domain_baset>> objectst;
  #else
  typedef std::unordered_map<
    irep_idt, std::unique_ptr<range_domain_baset>, string_hash> objectst;
  #endif

  virtual ~rw_range_sett();

  explicit rw_range_sett(const namespacet &_ns):
    ns(_ns)
  {
  }

  const objectst &get_r_set() const
  {
    return r_range_set;
  }

  const objectst &get_w_set() const
  {
    return w_range_set;
  }

  const range_domaint &get_ranges(objectst::const_iterator it) const
  {
    PRECONDITION(dynamic_cast<range_domaint*>(it->second.get())!=nullptr);
    return static_cast<const range_domaint &>(*it->second);
  }

  enum class get_modet { LHS_W, READ };

  virtual void get_objects_rec(
    const irep_idt &,
    goto_programt::const_targett,
    get_modet mode,
    const exprt &expr)
  {
    get_objects_rec(mode, expr);
  }

  virtual void get_objects_rec(
    const irep_idt &,
    goto_programt::const_targett,
    const typet &type)
  {
    get_objects_rec(type);
  }

  void output(std::ostream &out) const;

protected:
  const namespacet &ns;

  objectst r_range_set, w_range_set;

  virtual void get_objects_rec(
    get_modet mode,
    const exprt &expr);

  virtual void get_objects_rec(const typet &type);

  virtual void get_objects_complex_real(
    get_modet mode,
    const complex_real_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_complex_imag(
    get_modet mode,
    const complex_imag_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_if(
    get_modet mode,
    const if_exprt &if_expr,
    const range_spect &range_start,
    const range_spect &size);

  // overload to include expressions read/written
  // through dereferencing
  virtual void get_objects_dereference(
    get_modet mode,
    const dereference_exprt &deref,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_byte_extract(
    get_modet mode,
    const byte_extract_exprt &be,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_shift(
    get_modet mode,
    const shift_exprt &shift,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_member(
    get_modet mode,
    const member_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_index(
    get_modet mode,
    const index_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_array(
    get_modet mode,
    const array_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_struct(
    get_modet mode,
    const struct_exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_typecast(
    get_modet mode,
    const typecast_exprt &tc,
    const range_spect &range_start,
    const range_spect &size);

  virtual void get_objects_address_of(const exprt &object);

  virtual void get_objects_rec(
    get_modet mode,
    const exprt &expr,
    const range_spect &range_start,
    const range_spect &size);

  virtual void add(
    get_modet mode,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end);
};

inline std::ostream &operator << (
  std::ostream &out,
  const rw_range_sett &rw_set)
{
  rw_set.output(out);
  return out;
}

class value_setst;

class rw_range_set_value_sett:public rw_range_sett
{
public:
  rw_range_set_value_sett(
    const namespacet &_ns,
    value_setst &_value_sets):
    rw_range_sett(_ns),
    value_sets(_value_sets)
  {
  }

  void get_objects_rec(
    const irep_idt &_function,
    goto_programt::const_targett _target,
    get_modet mode,
    const exprt &expr) override
  {
    function = _function;
    target=_target;

    rw_range_sett::get_objects_rec(mode, expr);
  }

  void get_objects_rec(
    const irep_idt &_function,
    goto_programt::const_targett _target,
    const typet &type) override
  {
    function = _function;
    target = _target;

    rw_range_sett::get_objects_rec(type);
  }

protected:
  value_setst &value_sets;
  irep_idt function;
  goto_programt::const_targett target;

  using rw_range_sett::get_objects_rec;

  void get_objects_dereference(
    get_modet mode,
    const dereference_exprt &deref,
    const range_spect &range_start,
    const range_spect &size) override;
};

class guarded_range_domaint:public range_domain_baset
{
  typedef std::multimap<range_spect, std::pair<range_spect, exprt>> sub_typet;
  sub_typet data;

public:
  virtual void output(const namespacet &ns, std::ostream &out) const override;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef sub_typet::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef sub_typet::const_iterator const_iterator;

  iterator begin() { return data.begin(); }
  const_iterator begin() const { return data.begin(); }
  const_iterator cbegin() const { return data.begin(); }

  iterator end() { return data.end(); }
  const_iterator end() const { return data.end(); }
  const_iterator cend() const { return data.end(); }

  iterator insert(const sub_typet::value_type &v)
  {
    return data.insert(v);
  }

  iterator insert(sub_typet::value_type &&v)
  {
    return data.insert(std::move(v));
  }
};

class rw_guarded_range_set_value_sett:public rw_range_set_value_sett
{
public:
  rw_guarded_range_set_value_sett(
    const namespacet &_ns,
    value_setst &_value_sets):
    rw_range_set_value_sett(_ns, _value_sets)
  {
  }

  const guarded_range_domaint &get_ranges(objectst::const_iterator it) const
  {
    PRECONDITION(
      dynamic_cast<guarded_range_domaint*>(it->second.get())!=nullptr);
    return static_cast<const guarded_range_domaint &>(*it->second);
  }

  void get_objects_rec(
    const irep_idt &_function,
    goto_programt::const_targett _target,
    get_modet mode,
    const exprt &expr) override
  {
    guard = true_exprt();

    rw_range_set_value_sett::get_objects_rec(_function, _target, mode, expr);
  }

  void get_objects_rec(
    const irep_idt &function,
    goto_programt::const_targett target,
    const typet &type) override
  {
    rw_range_sett::get_objects_rec(function, target, type);
  }

protected:
  guardt guard;

  using rw_range_sett::get_objects_rec;

  void get_objects_if(
    get_modet mode,
    const if_exprt &if_expr,
    const range_spect &range_start,
    const range_spect &size) override;

  void add(
    get_modet mode,
    const irep_idt &identifier,
    const range_spect &range_start,
    const range_spect &range_end) override;
};

#endif // CPROVER_ANALYSES_GOTO_RW_H
