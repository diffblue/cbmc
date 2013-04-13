/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_INVARIANT_SET_H
#define CPROVER_CEGAR_INVARIANT_SET_H

/*
#include <ref_expr_set.h>

*/

#include <util/std_code.h>
#include <util/numbering.h>
#include <util/union_find.h>
#include <util/threeval.h>
#include <util/mp_arith.h>
#include <util/interval.h>

#include <pointer-analysis/value_sets.h>

class inv_object_storet
{
public:
  inv_object_storet(const namespacet &_ns):ns(_ns)
  {
  }

  bool get(const exprt &expr, unsigned &n);
  
  unsigned add(const exprt &expr);
  
  bool is_constant(unsigned n) const;
  bool is_constant(const exprt &expr) const;

  static bool is_constant_address(const exprt &expr);
  
  const irep_idt &operator[](unsigned n) const
  {
    return map[n];
  }

  const exprt &get_expr(unsigned n) const
  {
    assert(n<entries.size());
    return entries[n].expr;
  }
  
  void output(std::ostream &out) const;
  
  std::string to_string(
    unsigned n,
    const irep_idt &identifier) const;

protected:
  const namespacet &ns;

  typedef hash_numbering<irep_idt, irep_id_hash> mapt;
  mapt map;
  
  struct entryt
  {
    bool is_constant;
    exprt expr;
  };
  
  std::vector<entryt> entries;
  
  std::string build_string(const exprt &expr) const;

  static bool is_constant_address_rec(const exprt &expr);
};

class invariant_sett
{
public:
  // equalities ==
  unsigned_union_find eq_set;
  
  // <=
  typedef std::set<std::pair<unsigned, unsigned> > ineq_sett;
  ineq_sett le_set;
  
  // !=
  ineq_sett ne_set;
  
  // bounds
  typedef interval<mp_integer> boundst;
  typedef std::map<unsigned, boundst> bounds_mapt;
  bounds_mapt bounds_map;
  
  bool threaded;
  bool is_false;
  
  invariant_sett():
    threaded(false),
    is_false(false),
    value_sets(NULL),
    object_store(NULL),
    ns(NULL)
  {
  }
  
  void output(
    const irep_idt &identifier,
    std::ostream &out) const;

  // true = added s.th.
  bool make_union(const invariant_sett &other_invariants);
    
  void strengthen(const exprt &expr);
  
  void make_true()
  {
    eq_set.clear();
    le_set.clear();
    ne_set.clear();
    is_false=false;
  }

  void make_false()
  {
    eq_set.clear();
    le_set.clear();
    ne_set.clear();
    is_false=true;
  }

  void make_threaded()
  {
    make_true();
    threaded=true;
  }

  void apply_code(
    const codet &code);

  void modifies(
    const exprt &lhs);

  void assignment(
    const exprt &lhs,
    const exprt &rhs);
    
  void set_value_sets(value_setst &_value_sets)
  {
    value_sets=&_value_sets;
  }

  void set_object_store(inv_object_storet &_object_store)
  {
    object_store=&_object_store;
  }
  
  void set_namespace(const namespacet &_ns)
  {
    ns=&_ns;
  }
  
  static void intersection(ineq_sett &dest, const ineq_sett &other)
  {
    ineq_sett::iterator it_d=dest.begin();
  
    while(it_d!=dest.end())
    {
      ineq_sett::iterator next_d(it_d);
      next_d++;

      if(other.find(*it_d)==other.end())
        dest.erase(it_d);
      
      it_d=next_d;
    }  
  }
  
  static void remove(ineq_sett &dest, unsigned a)
  {
    for(ineq_sett::iterator it=dest.begin();
        it!=dest.end();
        ) // no it++
    {
      ineq_sett::iterator next(it);
      next++;

      if(it->first==a || it->second==a)
        dest.erase(it);

      it=next;
    }
  }
  
  tvt implies(const exprt &expr) const;
  
  void simplify(exprt &expr) const;
  
protected:
  value_setst *value_sets;
  inv_object_storet *object_store;
  const namespacet *ns;
  
  tvt implies_rec(const exprt &expr) const;
  static void nnf(exprt &expr, bool negate=false);
  void strengthen_rec(const exprt &expr);
  
  void add_type_bounds(const exprt &expr, const typet &type);

  void add_bounds(unsigned a, const boundst &bound)
  {
    bounds_map[a].intersect_with(bound);
  }
  
  void get_bounds(unsigned a, boundst &dest) const;

  // true = added s.th.
  bool make_union_bounds_map(const bounds_mapt &other);

  void modifies(unsigned a);
  
  std::string to_string(
    unsigned a,
    const irep_idt &identifier) const;

  bool get_object(
    const exprt &expr,
    unsigned &n) const;
  
  exprt get_constant(const exprt &expr) const;

  // queries
  bool has_eq(const std::pair<unsigned, unsigned> &p) const
  {
    return eq_set.same_set(p.first, p.second);
  }
  
  bool has_le(const std::pair<unsigned, unsigned> &p) const
  {
    return le_set.find(p)!=le_set.end();
  }
  
  bool has_ne(const std::pair<unsigned, unsigned> &p) const
  {
    return ne_set.find(p)!=ne_set.end();
  }
  
  tvt is_eq(std::pair<unsigned, unsigned> p) const;
  tvt is_le(std::pair<unsigned, unsigned> p) const;
  
  tvt is_lt(std::pair<unsigned, unsigned> p) const
  {
    return is_le(p) && !is_eq(p);
  }
  
  tvt is_ge(std::pair<unsigned, unsigned> p) const
  {
    std::swap(p.first, p.second);
    return is_eq(p) || is_lt(p);
  }
  
  tvt is_gt(std::pair<unsigned, unsigned> p) const
  {
    return !is_le(p);
  }

  tvt is_ne(std::pair<unsigned, unsigned> p) const
  {
    return !is_eq(p);
  }

  void add(const std::pair<unsigned, unsigned> &p, ineq_sett &dest);

  void add_le(const std::pair<unsigned, unsigned> &p)
  {
    add(p, le_set);
  }
  
  void add_ne(const std::pair<unsigned, unsigned> &p)
  {
    add(p, ne_set);
  }

  void add_eq(const std::pair<unsigned, unsigned> &eq);

  void add_eq(
    ineq_sett &dest,
    const std::pair<unsigned, unsigned> &eq,
    const std::pair<unsigned, unsigned> &ineq);
};

#endif
