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

class invariant_set_domain_factoryt;

class invariant_propagationt:public
  ait<invariant_set_domaint>
{
public:
  invariant_propagationt(const namespacet &_ns, value_setst &_value_sets);

  const invariant_sett &lookup(locationt l) const
  {
    return (*this)[l].invariant_set;
  }

  void initialize(const irep_idt &function, const goto_programt &goto_program)
    override;

  void make_all_true();
  void make_all_false();

  void simplify(goto_programt &goto_program);
  void simplify(goto_functionst &goto_functions);

  typedef ait<invariant_set_domaint> baset;

protected:
  // Each invariant_set_domain needs access to a few of the fields of the
  // invariant_propagation object.  This is a historic design that predates
  // the current interfaces.  Removing it would require a substantial refactor.
  // A minimally-intrusive work around is for the domain factory to be a
  // friend of the analyser object and create domains with references to the
  // relevant fields.
  friend invariant_set_domain_factoryt;

  const namespacet &ns;
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

#endif // CPROVER_ANALYSES_INVARIANT_PROPAGATION_H
