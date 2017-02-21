/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#include <util/std_types.h>
#include <util/std_expr.h>

#include "pointer_abstract_object.h"


/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(const typet &t):
  abstract_objectt(t)
{
  assert(t.id()==ID_pointer);
}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   type - the type the abstract_object is representing
   top - is the abstract_object starting as top
   bottom - is the abstract_object starting as bottom

 Outputs:

 Purpose: Start the abstract object at either top or bottom or neither
          Asserts if both top and bottom are true

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(
  const typet &t, bool tp, bool bttm):
    abstract_objectt(t, tp, bttm)
{
  assert(t.id()==ID_pointer);
}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   old - the abstract object to copy from

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(
  const pointer_abstract_objectt &old):
    abstract_objectt(old)
{}

/*******************************************************************\

Function: pointer_abstract_objectt::pointer_abstract_objectt

  Inputs:
   expr - the expression to use as the starting pointer for an abstract object

 Outputs:

 Purpose:

\*******************************************************************/

pointer_abstract_objectt::pointer_abstract_objectt(const constant_exprt &e):
  abstract_objectt(e)
{
  assert(e.type().id()==ID_pointer);
}
