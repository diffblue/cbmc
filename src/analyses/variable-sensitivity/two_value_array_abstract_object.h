/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// The base type of all abstract array representations

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/abstract_aggregate_object.h>
#include <stack>

struct array_aggregate_typet {
  static const irep_idt TYPE_ID() { return ID_array; }
  static const irep_idt ACCESS_EXPR_ID() { return ID_index; }
  static typet read_type(const typet &, const typet &object_type) {
    array_typet array_type(to_array_type(object_type));
    return array_type.subtype();
  }

  static void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) {
    ++statistics.number_of_arrays;
  }
};

class two_value_array_abstract_objectt :
  public abstract_aggregate_objectt<two_value_array_abstract_objectt, array_aggregate_typet>
{
public:
  typedef abstract_aggregate_objectt<two_value_array_abstract_objectt, array_aggregate_typet> abstract_aggregate_baset;

  explicit two_value_array_abstract_objectt(const typet &type)
    : abstract_aggregate_baset(type) { }
  two_value_array_abstract_objectt(const typet& type, bool top, bool bottom)
    : abstract_aggregate_baset(type, top, bottom) { }
  two_value_array_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_aggregate_baset(expr, environment, ns) { }

protected:
  void statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override { }
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ARRAY_ABSTRACT_OBJECT_H
