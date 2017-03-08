/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_H

#include <set>

#include <util/mp_arith.h>
#include <util/reference_counting.h>

#include "object_numbering.h"
#include "value_sets.h"

class namespacet;

class value_sett
{
public:
  value_sett():location_number(0)
  {
  }

  static bool field_sensitive(
    const irep_idt &id,
    const typet &type,
    const namespacet &);

  unsigned location_number;
  irep_idt function;
  static object_numberingt object_numbering;

  typedef irep_idt idt;

  class objectt
  {
  public:
    objectt():offset_is_set(false)
    {
    }

    explicit objectt(const mp_integer &_offset):
      offset(_offset),
      offset_is_set(true)
    {
    }

    mp_integer offset;
    bool offset_is_set;
    bool offset_is_zero() const
    { return offset_is_set && offset.is_zero(); }
  };

  class object_map_dt:public std::map<unsigned, objectt>
  {
  public:
    object_map_dt() {}
    static const object_map_dt blank;
  };

  exprt to_expr(object_map_dt::const_iterator it) const;

  typedef reference_counting<object_map_dt> object_mapt;

  void set(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    dest.write()[it->first]=it->second;
  }

  bool insert(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    return insert(dest, it->first, it->second);
  }

  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), objectt());
  }

  bool insert(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset) const
  {
    return insert(dest, object_numbering.number(src), objectt(offset));
  }

  bool insert(object_mapt &dest, unsigned n, const objectt &object) const;

  bool insert(object_mapt &dest, const exprt &expr, const objectt &object) const
  {
    return insert(dest, object_numbering.number(expr), object);
  }

  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    std::string suffix;
    typet declared_on_type;
    entryt()
    {
    }

    entryt(const idt &_identifier, const std::string &_suffix):
      identifier(_identifier),
      suffix(_suffix)
    {
    }

    entryt(
      const idt &_identifier,
      const std::string &_suffix,
      const typet &_declared_on_type):
      identifier(_identifier),
      suffix(_suffix),
      declared_on_type(_declared_on_type)
    {
    }
  };

  typedef std::set<exprt> expr_sett;

  #ifdef USE_DSTRING
  typedef std::map<idt, entryt> valuest;
  #else
  typedef std::unordered_map<idt, entryt, string_hash> valuest;
  #endif

  void get_value_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  expr_sett &get(
    const idt &identifier,
    const std::string &suffix);

  void make_any()
  {
    values.clear();
  }

  void clear()
  {
    values.clear();
  }

  entryt &get_entry(
    const entryt &e, const typet &type,
    const namespacet &);

  void output(
    const namespacet &ns,
    std::ostream &out) const;

  valuest values;

  // true = added s.th. new
  bool make_union(object_mapt &dest, const object_mapt &src) const;

  // true = added s.th. new
  bool make_union(const valuest &new_values);

  // true = added s.th. new
  bool make_union(const value_sett &new_values)
  {
    return make_union(new_values.values);
  }

  void guard(
    const exprt &expr,
    const namespacet &ns);

  virtual void apply_code(
    const codet &code,
    const namespacet &ns);

  virtual void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool is_simplified,
    bool add_to_sets);

  void do_function_call(
    const irep_idt &function,
    const exprt::operandst &arguments,
    const namespacet &ns);

  // edge back to call site
  void do_end_function(
    const exprt &lhs,
    const namespacet &ns);

  void get_reference_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  bool eval_pointer_offset(
    exprt &expr,
    const namespacet &ns) const;

protected:
  virtual void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns) const;

  virtual void get_value_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    bool is_simplified) const;

  virtual void get_reference_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const
  {
    get_reference_set_rec(expr, dest, ns);
  }

  virtual void get_reference_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const;

  virtual void dereference_rec(
    const exprt &src,
    exprt &dest) const;

  virtual void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    bool add_to_sets);

  void do_free(
    const exprt &op,
    const namespacet &ns);

  exprt make_member(
    const exprt &src,
    const irep_idt &component_name,
    const namespacet &ns);
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_H
