/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set (Flow Insensitive, Sharing)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H

#include <list>
#include <map>
#include <set>
#include <unordered_set>

#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/reference_counting.h>

#include "object_numbering.h"

class value_set_fit
{
public:
  value_set_fit():
  changed(false)
  // to_function, to_target_index are set by set_to()
  // from_function, from_target_index are set by set_from()
  {
  }

  unsigned to_function, from_function;
  unsigned to_target_index, from_target_index;
  static object_numberingt object_numbering;
  static hash_numbering<irep_idt, irep_id_hash> function_numbering;

  void set_from(const irep_idt &function, unsigned inx)
  {
    from_function = function_numbering.number(function);
    from_target_index = inx;
  }

  void set_to(const irep_idt &function, unsigned inx)
  {
    to_function = function_numbering.number(function);
    to_target_index = inx;
  }

  typedef irep_idt idt;

  /// Represents the offset into an object: either a unique integer offset,
  /// or an unknown value, represented by `!offset`.
  typedef optionalt<mp_integer> offsett;
  bool offset_is_zero(const offsett &offset) const
  {
    return offset && offset->is_zero();
  }

  class object_map_dt
  {
    typedef std::map<object_numberingt::number_type, offsett> data_typet;
    data_typet data;

  public:
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::iterator iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::const_iterator const_iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::value_type value_type;

    iterator begin() { return data.begin(); }
    const_iterator begin() const { return data.begin(); }
    const_iterator cbegin() const { return data.cbegin(); }

    iterator end() { return data.end(); }
    const_iterator end() const { return data.end(); }
    const_iterator cend() const { return data.cend(); }

    size_t size() const { return data.size(); }

    offsett &operator[](object_numberingt::number_type i)
    {
      return data[i];
    }

    template <typename It>
    void insert(It b, It e) { data.insert(b, e); }

    template <typename T>
    const_iterator find(T &&t) const { return data.find(std::forward<T>(t)); }

    static const object_map_dt blank;

  protected:
    ~object_map_dt()=default;
  };

  exprt to_expr(const object_map_dt::value_type &it) const;

  typedef reference_counting<object_map_dt> object_mapt;

  void set(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    dest.write()[it.first]=it.second;
  }

  bool insert(object_mapt &dest, const object_map_dt::value_type &it) const
  {
    return insert(dest, it.first, it.second);
  }

  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), offsett());
  }

  bool insert(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset_value) const
  {
    return insert(dest, object_numbering.number(src), offsett(offset_value));
  }

  bool insert(
    object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const
  {
    if(dest.read().find(n)==dest.read().end())
    {
      // new
      dest.write()[n] = offset;
      return true;
    }
    else
    {
      offsett &old_offset = dest.write()[n];

      if(old_offset && offset)
      {
        if(*old_offset == *offset)
          return false;
        else
        {
          old_offset.reset();
          return true;
        }
      }
      else if(!old_offset)
        return false;
      else
      {
        old_offset.reset();
        return true;
      }
    }
  }

  bool insert(object_mapt &dest, const exprt &expr, const offsett &offset) const
  {
    return insert(dest, object_numbering.number(expr), offset);
  }

  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    std::string suffix;

    entryt()
    {
    }

    entryt(const idt &_identifier, const std::string _suffix):
      identifier(_identifier),
      suffix(_suffix)
    {
    }
  };

  typedef std::unordered_set<exprt, irep_hash> expr_sett;

  typedef std::unordered_set<unsigned int> dynamic_object_id_sett;

  #ifdef USE_DSTRING
  typedef std::map<idt, entryt> valuest;
  typedef std::set<idt> flatten_seent;
  typedef std::unordered_set<idt> gvs_recursion_sett;
  typedef std::unordered_set<idt> recfind_recursion_sett;
  typedef std::unordered_set<idt> assign_recursion_sett;
  #else
  typedef std::unordered_map<idt, entryt, string_hash> valuest;
  typedef std::unordered_set<idt, string_hash> flatten_seent;
  typedef std::unordered_set<idt, string_hash> gvs_recursion_sett;
  typedef std::unordered_set<idt, string_hash> recfind_recursion_sett;
  typedef std::unordered_set<idt, string_hash> assign_recursion_sett;
  #endif

  void get_value_set(
    const exprt &expr,
    std::list<exprt> &dest,
    const namespacet &ns) const;

  expr_sett &get(
    const idt &identifier,
    const std::string &suffix);

  void clear()
  {
    values.clear();
  }

  void add_var(const idt &id, const std::string &suffix)
  {
    get_entry(id, suffix);
  }

  void add_var(const entryt &e)
  {
    get_entry(e.identifier, e.suffix);
  }

  entryt &get_entry(const idt &id, const std::string &suffix)
  {
    return get_entry(entryt(id, suffix));
  }

  entryt &get_entry(const entryt &e)
  {
    std::string index=id2string(e.identifier)+e.suffix;

    std::pair<valuest::iterator, bool> r=
      values.insert(std::pair<idt, entryt>(index, e));

    return r.first->second;
  }

  void add_vars(const std::list<entryt> &vars)
  {
    for(std::list<entryt>::const_iterator
        it=vars.begin();
        it!=vars.end();
        it++)
      add_var(*it);
  }

  void output(
    const namespacet &ns,
    std::ostream &out) const;

  valuest values;

  bool changed;

  // true = added something new
  bool make_union(object_mapt &dest, const object_mapt &src) const;

  // true = added something new
  bool make_union(const valuest &new_values);

  // true = added something new
  bool make_union(const value_set_fit &new_values)
  {
    return make_union(new_values.values);
  }

  void apply_code(
    const exprt &code,
    const namespacet &ns);

  void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns);

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
    expr_sett &expr_set,
    const namespacet &ns) const;

protected:
  void get_reference_set_sharing(
    const exprt &expr,
    expr_sett &expr_set,
    const namespacet &ns) const;

  void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns,
    gvs_recursion_sett &recursion_set) const;


  void get_value_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const;

  void get_reference_set_sharing(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const
  {
    get_reference_set_sharing_rec(expr, dest, ns);
  }

  void get_reference_set_sharing_rec(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const;

  void dereference_rec(
    const exprt &src,
    exprt &dest) const;

  void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    assign_recursion_sett &recursion_set);

  void flatten(const entryt &e, object_mapt &dest) const;

  void flatten_rec(
    const entryt&,
    object_mapt&,
    flatten_seent&) const;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H
