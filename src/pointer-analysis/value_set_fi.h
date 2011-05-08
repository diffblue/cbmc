/*******************************************************************\

Module: Value Set (Flow Insensitive, Sharing)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef VALUE_SET_FI_H_
#define VALUE_SET_FI_H_

#include <set>

#include <mp_arith.h>
#include <namespace.h>
#include <reference_counting.h>

#include "object_numbering.h"

class value_set_fit
{
public:
  value_set_fit()
  {
  }

  unsigned to_function, from_function;
  unsigned to_target_index, from_target_index;
  static object_numberingt object_numbering;
  static hash_numbering<irep_idt, irep_id_hash> function_numbering;
  
  void set_from(const irep_idt& function, unsigned inx)
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
  
  static const std::string &id2string(const idt &id)
  {
    #ifdef USE_DSTRING
    return id.as_string();
    #else
    return id;
    #endif
  }

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
    const static object_map_dt empty;    
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
  
  bool insert(object_mapt &dest, const exprt &src, const mp_integer &offset) const
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
  
  typedef hash_set_cont<exprt, irep_hash> expr_sett;

  static void add_objects(const entryt &src, expr_sett &dest);

  #ifdef USE_DSTRING   
  typedef std::map<idt, entryt> valuest;
  typedef std::set<idt> flatten_seent;
  typedef hash_set_cont<idt, irep_id_hash> gvs_recursion_sett;
  typedef hash_set_cont<idt, irep_id_hash> recfind_recursion_sett;
  typedef hash_set_cont<idt, irep_id_hash> assign_recursion_sett;
  #else
  typedef hash_map_cont<idt, entryt, string_hash> valuest;
  typedef hash_set_cont<idt, string_hash> flatten_seent;
  typedef hash_set_cont<idt, string_hash> gvs_recursion_sett;
  typedef hash_set_cont<idt, string_hash> recfind_recursion_sett;
  typedef hash_set_cont<idt, string_hash> assign_recursion_sett;
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
  
  // true = added s.th. new
  bool make_union(object_mapt &dest, const object_mapt &src) const;

  // true = added s.th. new
  bool make_union(const valuest &new_values);

  // true = added s.th. new
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
  
  void flatten_rec( const entryt&, 
                    object_mapt&, 
                    flatten_seent&) const;
};

#endif /*VALUE_SET_FI_H_*/
