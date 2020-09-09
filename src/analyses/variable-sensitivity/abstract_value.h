/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// The parent class of all abstractions that represent a base type

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H

#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_valuet : public abstract_objectt
{
public:
  /// \param type: the type the abstract_value is representing
  explicit abstract_valuet(const typet &type);

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_value is representing
  /// \param top: is the abstract_value starting as top
  /// \param bottom: is the abstract_value starting as bottom
  abstract_valuet(const typet &type, bool top, bool bottom);

  /// Construct an abstract value from the expression
  ///
  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: The environment this abstract object is
  ///                     being created in
  /// \param ns: the namespace
  abstract_valuet(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual ~abstract_valuet()
  {
  }

protected:
  CLONE
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_VALUE_H
