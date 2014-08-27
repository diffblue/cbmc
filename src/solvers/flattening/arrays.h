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

  void build_index_map();
  void update_index_map();
  void collect_arrays(const exprt &a);
};

#endif
