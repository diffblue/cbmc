/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set (Flow Insensitive, Sharing)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H

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

  using idt = irep_idt;

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

  class object_map_dt
  {
    using data_typet = std::map<unsigned, objectt>;
    data_typet data;

  public:
    // NOLINTNEXTLINE(readability/identifiers)
    using iterator = data_typet::iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    using const_iterator = data_typet::const_iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    using value_type = data_typet::value_type;

    iterator begin() { return data.begin(); }
    const_iterator begin() const { return data.begin(); }
    const_iterator cbegin() const { return data.cbegin(); }

    iterator end() { return data.end(); }
    const_iterator end() const { return data.end(); }
    const_iterator cend() const { return data.cend(); }

    size_t size() const { return data.size(); }

    objectt &operator[](unsigned i) { return data[i]; }

    template <typename It>
    void insert(It b, It e) { data.insert(b, e); }

    template <typename T>
    const_iterator find(T &&t) const { return data.find(std::forward<T>(t)); }

    static const object_map_dt blank;

  protected:
    ~object_map_dt()=default;
  };

  exprt to_expr(const object_map_dt::value_type &it) const;

  using object_mapt = reference_counting<object_map_dt>;

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
    return insert(dest, object_numbering.number(src), objectt());
  }

  bool insert(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset) const
  {
    return insert(dest, object_numbering.number(src), objectt(offset));
  }

  bool insert(object_mapt &dest, unsigned n, const objectt &object) const
  {
    if(dest.read().find(n)==dest.read().end())
    {
      // new
      dest.write()[n]=object;
      return true;
    }
    else
    {
      objectt &old=dest.write()[n];

      if(old.offset_is_set && object.offset_is_set)
      {
        if(old.offset==object.offset)
          return false;
        else
        {
          old.offset_is_set=false;
          return true;
        }
      }
      else if(!old.offset_is_set)
        return false;
      else
      {
        old.offset_is_set=false;
        return true;
      }
    }
  }

  bool insert(object_mapt &dest, const exprt &expr, const objectt &object) const
  {
    return insert(dest, object_numbering.number(expr), object);
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

  using expr_sett = std::unordered_set<exprt, irep_hash>;

  using dynamic_object_id_sett = std::unordered_set<unsigned int>;

  #ifdef USE_DSTRING
  using valuest = std::map<idt, entryt>;
  using flatten_seent = std::set<idt>;
  using gvs_recursion_sett = std::unordered_set<idt, irep_id_hash>;
  using recfind_recursion_sett = std::unordered_set<idt, irep_id_hash>;
  using assign_recursion_sett = std::unordered_set<idt, irep_id_hash>;
  #else
  using valuest = std::unordered_map<idt, entryt, string_hash>;
  using flatten_seent = std::unordered_set<idt, string_hash>;
  using gvs_recursion_sett = std::unordered_set<idt, string_hash>;
  using recfind_recursion_sett = std::unordered_set<idt, string_hash>;
  using assign_recursion_sett = std::unordered_set<idt, string_hash>;
  #endif

  void get_value_set(
    const exprt &expr,
    std::list<exprt> &dest,
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

  void do_free(
    const exprt &op,
    const namespacet &ns);

  void flatten(const entryt &e, object_mapt &dest) const;

  void flatten_rec(
    const entryt&,
    object_mapt&,
    flatten_seent&) const;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_FI_H
