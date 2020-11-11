/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/type.h>

#include "abstract_value.h"

abstract_valuet::abstract_valuet(const typet &type) : abstract_objectt(type)
{
}

abstract_valuet::abstract_valuet(const typet &type, bool top, bool bottom)
  : abstract_objectt(type, top, bottom)
{
}

abstract_valuet::abstract_valuet(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_objectt(expr, environment, ns)
{
}
