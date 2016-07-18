/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_H

#include <climits>
#include <set>

#include <util/mp_arith.h>
#include <util/reference_counting.h>
#include <util/irep_hash.h>
#include <util/string_hash.h>

#include "object_numbering.h"
#include "value_sets.h"

#include <iostream>

#define VALUE_SET_TOP

class namespacet;

class value_sett
{
public:
  value_sett(bool _use_top=true)
   : location_number(0), is_bottom(true), use_top(_use_top)
  {
  }

  static bool field_sensitive(
    const irep_idt &id,
    const typet &type,
    const namespacet &);

  unsigned location_number;
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
  
#if 0
    bool operator==(const objectt other) const
    {
      return (offset==other.offset) &&
        (offset_is_set==other.offset_is_set);
    }
#endif

    mp_integer offset;
    bool offset_is_set;

    bool offset_is_zero() const
    {
      return offset_is_set && offset.is_zero();
    }

    size_t hash() const
    {
      size_t result;
      string_hash hash;

      result=(size_t)offset_is_set;

      if(offset_is_set)
      {
        std::string s=integer2string(offset);
        result=hash_combine(result, hash(s));
        result=hash_finalize(result, 1);
      }

      return result;
    }

    bool operator==(const objectt &other) const
    {
      if(offset_is_set!=other.offset_is_set)
        return false;

      if(!offset_is_set && !other.offset_is_set)
        return true;

      return offset==other.offset;
    }
  };
  
  class object_map_dt:public std::map<unsigned, objectt>
  {
  public:
    object_map_dt() : use_top(true), top(false) {}
    object_map_dt(bool _use_top) : use_top(_use_top), top(false) {}
    bool use_top, top;
    void make_top();
    bool is_top() const;
    static bool is_top(const std::pair<unsigned, objectt> &o);
    const static object_map_dt blank;

    size_t hash() const
    {
      assert(use_top);

      size_t result;
      result=(size_t)top;

      if(!top)
      {
        for(std::map<unsigned, objectt>::const_iterator it=begin();
            it!=end(); it++)
        {
          result=hash_combine(result, (size_t)it->first);
          result=hash_combine(result, it->second.hash());
        }

        result=hash_finalize(result, size()*2);
      }

      return result;
    }

    bool operator==(const object_map_dt &other) const
    {
      assert(use_top);

      if(top!=other.top)
        return false;

      if(top && other.top)
        return true;

      const std::map<unsigned, objectt> &base=*this;
      const std::map<unsigned, objectt> &other_base=other;

      return base==other_base;
    }
  };
  
  exprt to_expr(object_map_dt::const_iterator it) const;
  
  typedef reference_counting<object_map_dt> object_mapt;
  
  static bool overlap(
    const object_mapt &om1,
    const object_mapt &om2,
    bool &inconclusive);
  
  void set(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    dest.write()[it->first]=it->second;
  }

  static bool insert(object_mapt &dest, object_map_dt::const_iterator it)
  {
    return insert(dest, it->first, it->second);
  }

  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), objectt());
  }
  
  bool insert(object_mapt &dest, const exprt &src, const mp_integer &offset) const
  {
    return insert(dest, object_numbering.number(src), objectt(offset));
  }
  
  static bool insert(object_mapt &dest, unsigned n, const objectt &object);
  
  bool insert(object_mapt &dest, const exprt &expr, const objectt &object) const
  {
    return insert(dest, object_numbering.number(expr), object);
  }
  
  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    idt suffix;
    
    entryt() : object_map(false)
    {
    }
    
    entryt(const idt &_identifier, const std::string &_suffix, bool use_top=true):
      object_map(use_top), identifier(_identifier),
      suffix(_suffix)
    {
    }

    size_t hash() const
    {
      irep_id_hash id_hash;
      size_t result;

      result=hash_combine(id_hash(identifier), id_hash(suffix));

      const object_map_dt &om=object_map.read();
      result=hash_combine(result, om.hash());

      result=hash_finalize(result, 2);

      return result;
    }

    bool operator==(const entryt &other) const
    {
      return object_map==other.object_map &&
             identifier==other.identifier &&
             suffix==other.suffix;
    }
  };
  
  typedef std::set<exprt> expr_sett;

  #ifdef USE_DSTRING   
  typedef std::map<idt, entryt> valuest;
  #else
  typedef hash_map_cont<idt, entryt, string_hash> valuest;
  #endif

  void get_value_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns,
    unsigned don=UINT_MAX) const;

  expr_sett &get(
    const idt &identifier,
    const std::string &suffix);

  void make_any()
  {
    values.clear();
    is_bottom = false;
  }
  
  void clear()
  {
    values.clear();
    is_bottom = true;
  }
  
  entryt &get_entry(
    const entryt &e, const typet &type,
    const namespacet &);
  
  void output(
    const namespacet &ns,
    std::ostream &out) const;
    
  static void output(
      const namespacet &ns,
      std::ostream &out,
      const object_mapt &object_map);
  
  valuest values;
  bool is_bottom;
  
  // true = added s.th. new
  static bool make_union(object_mapt &dest, const object_mapt &src);

  // true = removed s.th.
  static bool make_intersection(object_mapt &dest, const object_mapt &src);

  // true = added s.th. new
  bool make_union(const valuest &new_values);

  // true = added s.th. new
  bool make_union(const value_sett &new_values)
  {
    if(is_bottom && new_values.is_bottom)
      return false;
    bool result = is_bottom && !new_values.is_bottom;
    is_bottom = false;
    return make_union(new_values.values) || result;
  }
  
  // true = added s.th. new
  bool make_union(const valuest &new_values, 
    hash_set_cont<irep_idt, irep_id_hash> &selected_vars);
  
  void guard(
    const exprt &expr,
    const namespacet &ns,
    unsigned don);
  
  void apply_code(
    const codet &code,
    const namespacet &ns,
    unsigned don=UINT_MAX);

  void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool is_simplified,
    bool add_to_sets,
    unsigned don=UINT_MAX);

  void do_function_call(
    const irep_idt &function,
    const exprt::operandst &arguments,
    const namespacet &ns,
    unsigned don);

  void remove_parameters(
    const irep_idt id, // function
    const namespacet &ns);

  // edge back to call site
  void do_end_function(
    const exprt &lhs,
    const namespacet &ns,
    unsigned don);

  void get_reference_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns,
    unsigned don=UINT_MAX) const;

  bool eval_pointer_offset(
    exprt &expr,
    const namespacet &ns,
    unsigned don) const;

  void get_reference_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    unsigned don=UINT_MAX) const
  {
    get_reference_set_rec(expr, dest, ns, don);
  }

  void get_value_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    bool is_simplified,
    unsigned don=UINT_MAX) const;

  size_t hash() const
  {
    assert(use_top);
    assert(location_number==0);

    irep_id_hash id_hash;
    size_t result;

    result=(size_t)is_bottom;

    if(!is_bottom)
    {
      for(valuest::const_iterator it=values.begin();
          it!=values.end(); it++)
  {
        result=hash_combine(result, id_hash(it->first));
        result=hash_combine(result, it->second.hash());
  }

      result=hash_finalize(result, values.size()*2);
    }

    return result;
  }

  bool operator==(const value_sett &other) const
  {
    if(is_bottom!=other.is_bottom)
      return false;

    if(is_bottom && other.is_bottom)
      return true;

    return values==other.values;
  }

  bool use_top;
protected:

  void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns,
    unsigned don) const;

  void get_reference_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    unsigned don) const;

  void dereference_rec(
    const exprt &src,
    exprt &dest) const;

  void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    bool add_to_sets,
    unsigned don);

  void initialize(
    const exprt &expr,
    const namespacet &ns,
    unsigned don);

  void initialize_rec(
    const exprt &expr,
    const namespacet &ns,
    unsigned don);

  void do_free(
    const exprt &op,
    const namespacet &ns,
    unsigned don);
    
  exprt make_member(
    const exprt &src, 
    const irep_idt &component_name,
    const namespacet &ns);
};

#endif
