/*******************************************************************\

Module: Invariant Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_INVARIANT_PROPAGATION_H
#define CPROVER_CEGAR_INVARIANT_PROPAGATION_H

#include <pointer-analysis/value_sets.h>

#include "static_analysis.h"
#include "invariant_set_domain.h"

class invariant_propagationt:public
  static_analysist<invariant_set_domaint>
{
public:
  invariant_propagationt(
    const namespacet &_ns,
    value_setst &_value_sets):
    static_analysist<invariant_set_domaint>(_ns),
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
  
  typedef static_analysist<invariant_set_domaint> baset;
  
protected:
  value_setst &value_sets;
  
  inv_object_storet object_store;

  typedef std::list<unsigned> object_listt;

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

#endif
