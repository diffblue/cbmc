/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

/// \file
/// The base of all union abstractions

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_UNION_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_UNION_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_aggregate_object.h>

class two_value_union_abstract_objectt : public abstract_aggregate_objectt<
                                           two_value_union_abstract_objectt,
                                           union_aggregate_typet>
{
public:
  typedef abstract_aggregate_objectt<
    two_value_union_abstract_objectt,
    union_aggregate_typet>
    abstract_aggregate_baset;

  /// \param type: the type the abstract_object is representing
  explicit two_value_union_abstract_objectt(const typet &type)
    : abstract_aggregate_baset(type)
  {
  }

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  two_value_union_abstract_objectt(const typet &type, bool top, bool bottom)
    : abstract_aggregate_baset(type, top, bottom)
  {
  }

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment the abstract object is going
  ///                     to be evaluated in.
  /// \param ns: the current namespace
  explicit two_value_union_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_aggregate_baset(expr, environment, ns)
  {
  }

protected:
  void statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override
  {
  }
};
#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_UNION_ABSTRACT_OBJECT_H
