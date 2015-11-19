/*******************************************************************\

Module: Theory of Arrays with Extensionality

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ARRAYS_H
#define CPROVER_ARRAYS_H

#include <set>

#include <util/union_find.h>

#include "equality.h"

class array_of_exprt;
class equal_exprt;
class if_exprt;
class index_exprt;
class with_exprt;
class update_exprt;

class arrayst:public equalityt
{
public:
  arrayst(const namespacet &_ns, propt &_prop);

  virtual void post_process()
  {
    post_process_arrays();
    SUB::post_process();
  }
  
  typedef equalityt SUB;
  
  literalt record_array_equality(const equal_exprt &expr);
  void record_array_index(const index_exprt &expr);

protected:
  virtual void post_process_arrays()
  {
    add_array_constraints();
  }

  struct array_equalityt
  {
    literalt l;
    exprt f1, f2;
  };

  // the list of all equalities between arrays
  // references to objects in this container need to be stable as
  // elements are added while references are held
  typedef std::list<array_equalityt> array_equalitiest;
  array_equalitiest array_equalities;
  
  // this is used to find the clusters of arrays being compared
  union_find<exprt> arrays;
  
  // this tracks the array indicies for each array
  typedef std::set<exprt> index_sett;
  // references to values in this container need to be stable as
  // elements are added while references are held
  typedef std::map<unsigned, index_sett> index_mapt;
  index_mapt index_map;
  
  // adds array constraints lazily
  typedef enum lazy_type {ARRAY_ACKERMANN, ARRAY_WITH, ARRAY_IF, ARRAY_OF, ARRAY_TYPECAST} lazy_typet;
  struct lazy_constraintt
  {
    lazy_typet type;
    exprt lazy;

    lazy_constraintt(lazy_typet _type, const exprt &_lazy)
    {
      type = _type;
      lazy = _lazy;
    }
  };

  bool lazy_arrays;
  bool incremental_cache;
  std::list<lazy_constraintt> lazy_array_constraints;
  void add_array_constraint(const lazy_constraintt &lazy, bool refine = true);
  std::map<exprt, bool> expr_map;

  // adds all the constraints eagerly
  void add_array_constraints();
  void add_array_Ackermann_constraints();
  void add_array_constraints_equality(const index_sett &index_set, const array_equalityt &array_equality);
  void add_array_constraints(const index_sett &index_set, const exprt &expr);
  void add_array_constraints(const index_sett &index_set, const array_equalityt &array_equality);
  void add_array_constraints_if(const index_sett &index_set, const if_exprt &exprt);
  void add_array_constraints_with(const index_sett &index_set, const with_exprt &expr);
  void add_array_constraints_update(const index_sett &index_set, const update_exprt &expr);
  void add_array_constraints_array_of(const index_sett &index_set, const array_of_exprt &exprt);

  void update_index_map(bool update_all);
  void update_index_map(unsigned i);
  std::set<unsigned> update_indices;
  void collect_arrays(const exprt &a);
  void collect_indices();
  void collect_indices(const exprt &a);
  
  virtual bool is_unbounded_array(const typet &type) const=0;
    // (maybe this function should be partially moved here from boolbv)
};

#endif
