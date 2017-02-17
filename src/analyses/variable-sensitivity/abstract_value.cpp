/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/type.h>

#include "abstract_value.h"

/*******************************************************************\

Function: abstract_valuet::abstract_valuet

  Inputs:
   type - the type the abstract_value is representing

 Outputs:

 Purpose:

\*******************************************************************/

abstract_valuet::abstract_valuet(const typet &type):
  abstract_objectt(type)
{}

/*******************************************************************\

Function: abstract_valuet::abstract_valuet

  Inputs:
   type - the type the abstract_value is representing
   top - is the abstract_value starting as top
   bottom - is the abstract_value starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

abstract_valuet::abstract_valuet(const typet &type, bool top, bool bottom):
  abstract_objectt(type, top, bottom)
{}

/*******************************************************************\

Function: abstract_valuet::abstract_valuet

  Inputs:
   old - the abstract value to copy from

 Outputs:

 Purpose:

\*******************************************************************/

abstract_valuet::abstract_valuet(const abstract_valuet &old):
  abstract_objectt(old)
{}

abstract_valuet::abstract_valuet(const constant_exprt &expr):
  abstract_objectt(expr)
{}
