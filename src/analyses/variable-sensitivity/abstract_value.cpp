/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/type.h>

#include "abstract_value.h"

/// Function: abstract_valuet::abstract_valuet
///
/// \param type: the type the abstract_value is representing
///
abstract_valuet::abstract_valuet(const typet &type) : abstract_objectt(type)
{
}

/// Function: abstract_valuet::abstract_valuet
///
/// \param type: the type the abstract_value is representing
/// \param top: is the abstract_value starting as top
/// \param bottom: is the abstract_value starting as bottom
///
/// Start the abstract object at either top or bottom or neither
/// Asserts if both top and bottom are true
abstract_valuet::abstract_valuet(const typet &type, bool top, bool bottom)
  : abstract_objectt(type, top, bottom)
{
}

/// Function: abstract_valuet::abstract_valuet
///
/// \param expr: the expression to use as the starting pointer for an abstract object
/// \param environment: The environment this abstract object is being created in
/// \param ns: the namespace
///
/// Construct an abstract value from the expression
abstract_valuet::abstract_valuet(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(expr, environment, ns)
{
}
