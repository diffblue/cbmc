/*******************************************************************\

Module: Invariant Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Propagation

#ifndef CPROVER_ANALYSES_INVARIANT_PROPAGATION_H
#define CPROVER_ANALYSES_INVARIANT_PROPAGATION_H

#include <pointer-analysis/value_sets.h>

#include "ai.h"
#include "invariant_set_domain.h"

class invariant_propagationt:public
  ait<invariant_set_domaint>
{
public:
  invariant_propagationt(
    const namespacet &_ns,
    value_setst &_value_sets):
    ait<invariant_set_domaint>(),
    ns(_ns),
    value_sets(_value_sets),
    object_store(_ns)
  {
  }

  const invariant_sett &lookup(locationt l) const
  {
    return (*this)[l].invariant_set;
  }

  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);

  void make_all_true();
  void make_all_false();

  void simplify(goto_programt &goto_program);
  void simplify(goto_functionst &goto_functions);

  using baset = ait<invariant_set_domaint>;

protected:
  const namespacet &ns;
  value_setst &value_sets;

  inv_object_storet object_store;

  using object_listt = std::list<unsigned int>;

  void add_objects(const goto_programt &goto_program);
  void add_objects(const goto_functionst &goto_functions);

  void get_objects(
    const symbolt &symbol,
    object_listt &dest);

  void get_objects_rec(
    const exprt &src,
    std::list<exprt> &dest);

  void get_globals(object_listt &globals);

  bool check_type(const typet &type) const;
};

#endif // CPROVER_ANALYSES_INVARIANT_PROPAGATION_H
