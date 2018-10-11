/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set (Flow Insensitive, Sharing, Validity Regions)

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_FIVR_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_FIVR_H

#include <list>
#include <map>
#include <unordered_set>

#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/reference_counting.h>
#include <util/invariant.h>

#include "object_numbering.h"

class value_set_fivrt
{
public:
  value_set_fivrt()
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
  public:
    object_map_dt() {}
    static const object_map_dt blank;

    typedef std::map<object_numberingt::number_type, offsett> objmapt;
    objmapt objmap;

    // NOLINTNEXTLINE(readability/identifiers)
    typedef objmapt::const_iterator const_iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef objmapt::iterator iterator;

    const_iterator find(object_numberingt::number_type k)
    {
      return objmap.find(k);
    }
    iterator begin() { return objmap.begin(); }
    const_iterator begin() const { return objmap.begin(); }
    iterator end() { return objmap.end(); }
    const_iterator end() const { return objmap.end(); }
    size_t size() const { return objmap.size(); }
    bool empty() const { return objmap.empty(); }
    void clear() { objmap.clear(); validity_ranges.clear(); }

    offsett &operator[](object_numberingt::number_type k)
    {
      return objmap[k];
    }

    // operator[] is the only way to insert something!
    std::pair<iterator, bool>
    insert(const std::pair<object_numberingt::number_type, offsett> &)
    {
      UNREACHABLE;
    }
    iterator
    insert(iterator, const std::pair<object_numberingt::number_type, offsett> &)
    {
      UNREACHABLE;
    }

    class validity_ranget
    {
    public:
      unsigned function;
      unsigned from, to;

      validity_ranget():
        function(0), from(0), to(0)
      {
      }

      validity_ranget(unsigned fnc, unsigned f, unsigned t):
        function(fnc), from(f), to(t)
      {
      }

      bool contains(unsigned f, unsigned line) const
      {
        return (function==f && from<=line && line<=to);
      }
    };

    typedef std::list<validity_ranget> vrange_listt;
    typedef std::map<unsigned, vrange_listt> validity_rangest;
    validity_rangest validity_ranges;

    bool set_valid_at(unsigned inx, unsigned f, unsigned line);
    bool set_valid_at(unsigned inx, const validity_ranget &vr);
    bool is_valid_at(unsigned inx, unsigned f, unsigned line) const;
  };

  exprt to_expr(object_map_dt::const_iterator it) const;

  typedef reference_counting<object_map_dt> object_mapt;

  void set(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    dest.write()[it->first]=it->second;
  }

  bool insert_to(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    return insert_to(dest, it->first, it->second);
  }

  bool insert_to(object_mapt &dest, const exprt &src) const
  {
    return insert_to(dest, object_numbering.number(src), offsett());
  }

  bool insert_to(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset_value) const
  {
    return insert_to(dest, object_numbering.number(src), offsett(offset_value));
  }

  bool insert_to(
    object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const;

  bool
  insert_to(object_mapt &dest, const exprt &expr, const offsett &offset) const
  {
    return insert_to(dest, object_numbering.number(expr), offset);
  }

  bool insert_from(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    return insert_from(dest, it->first, it->second);
  }

  bool insert_from(object_mapt &dest, const exprt &src) const
  {
    return insert_from(dest, object_numbering.number(src), offsett());
  }

  bool insert_from(
    object_mapt &dest,
    const exprt &src,
    const mp_integer &offset_value) const
  {
    return insert_from(
      dest, object_numbering.number(src), offsett(offset_value));
  }

  bool insert_from(
    object_mapt &dest,
    object_numberingt::number_type n,
    const offsett &offset) const;

  bool
  insert_from(object_mapt &dest, const exprt &expr, const offsett &offset) const
  {
    return insert_from(dest, object_numbering.number(expr), offset);
  }

  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    std::string suffix;

    entryt() { }

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
  typedef std::unordered_set<idt> flatten_seent;
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
    std::list<exprt> &expr_set,
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

  entryt &get_temporary_entry(const idt &id, const std::string &suffix)
  {
    std::string index=id2string(id)+suffix;
    return temporary_values[index];
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
  valuest temporary_values;

  // true = added something new
  bool make_union(
    object_mapt &dest,
    const object_mapt &src) const;

  bool make_valid_union(
    object_mapt &dest,
    const object_mapt &src) const;

  void copy_objects(
    object_mapt &dest,
    const object_mapt &src) const;

  void apply_code(
    const exprt &code,
    const namespacet &ns);

  bool handover();

  void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool add_to_sets=false);

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
    assign_recursion_sett &recursion_set,
    bool add_to_sets);

  void do_free(
    const exprt &op,
    const namespacet &ns);

  void flatten(
    const entryt &e,
    object_mapt &dest) const;

  void flatten_rec(
    const entryt&,
    object_mapt&,
    flatten_seent&,
    unsigned from_function) const;

  bool recursive_find(
    const irep_idt &ident,
    const object_mapt &rhs,
    recfind_recursion_sett &recursion_set) const;
};

#endif // CPROVER_POINTER_ANALYSIS_VALUE_SET_FIVR_H
