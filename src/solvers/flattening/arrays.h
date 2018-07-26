/*******************************************************************\

Module: Theory of Arrays with Extensionality

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Theory of Arrays with Extensionality

#ifndef CPROVER_SOLVERS_FLATTENING_ARRAYS_H
#define CPROVER_SOLVERS_FLATTENING_ARRAYS_H

#include <set>

#include <util/numbering.h>
#include <util/graph.h>

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

  void post_process() override
  {
    post_process_arrays();
    SUB::post_process();
  }

  // NOLINTNEXTLINE(readability/identifiers)
  typedef equalityt SUB;

  literalt record_array_equality(const equal_exprt &expr);
  void record_array_index(const index_exprt &expr);

protected:
  virtual void post_process_arrays()
  {
    add_array_constraints();
  }

  // adds all the constraints eagerly
  void add_array_constraints();
  void add_array_Ackermann_constraints();
  void collect_arrays(const exprt &);
  void collect_indices(const exprt &);

  class weg_edget
  {
  public:
    literalt condition;
    exprt update;
    weg_edget():
      condition(const_literal(true)),
      update(nil_exprt())
    {
    }
  };

  // weak equality graph
  class weg_nodet:public graph_nodet<weg_edget>
  {
    exprt array;
  };

  typedef grapht<weg_nodet> wegt;
  wegt weg;

  void expand_weg(wegt::node_indext index)
  {
    if(index>=weg.size())
      weg.resize(index+1);
  }

  void add_weg_edge(
    wegt::node_indext a1,
    wegt::node_indext a2,
    literalt cond)
  {
    expand_weg(a1);
    expand_weg(a2);
    weg.edge(a1, a2).condition=cond;
    weg.edge(a2, a1).condition=cond;
  }

  void add_weg_edge(
    wegt::node_indext a1,
    wegt::node_indext a2,
    const with_exprt &_update)
  {
    expand_weg(a1);
    expand_weg(a2);
    weg.edge(a1, a2).update=_update;
    weg.edge(a2, a1).update=_update;
  }

  // this is used to give a unique number to all arrays
  typedef numbering<exprt> array_numberingt;
  array_numberingt arrays;

  // this tracks the array indicies for each array
  typedef std::set<exprt> index_sett;
  typedef std::map<std::size_t, index_sett> index_mapt;
  index_mapt index_map;

  virtual bool is_unbounded_array(const typet &type) const=0;
    // (maybe this function should be partially moved here from boolbv)

  bool must_be_different(const exprt &, const exprt &);

  // path search
  struct stack_entryt
  {
    wegt::node_indext n;
    wegt::edgest::const_iterator edge, next;
    stack_entryt(
      wegt::node_indext _n,
      wegt::edgest::const_iterator _edge):
      n(_n), edge(_edge), next(_edge)
    {
    }
  };

  typedef std::vector<stack_entryt> weg_patht;
  void process_weg_path(const weg_patht &);

  void weg_path_condition(
    const weg_patht &,
    const exprt &index_a,
    exprt::operandst &cond);

  //bool incremental_cache;
};

#endif // CPROVER_SOLVERS_FLATTENING_ARRAYS_H
