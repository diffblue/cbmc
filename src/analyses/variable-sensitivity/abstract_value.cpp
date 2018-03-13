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
   expr - the expression to use as the starting pointer for an abstract object
   environment - The environment this abstract object is being created in
   ns - the namespace

 Outputs:

 Purpose: Construct an abstract value from the expression

\*******************************************************************/

abstract_valuet::abstract_valuet(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns):
    abstract_objectt(expr, environment, ns)
{}


void abstract_objectt::dump_map(
  std::ostream out, const abstract_objectt::shared_mapt &m)
{
  shared_mapt::viewt view;
  m.get_view(view);

  out << "{";
  bool first=true;
  for(auto &item : view)
  {
    out << (first ? "" : ", ") << item.first;
    first = false;
  }
  out << "}";
}

/**
 * \brief Dump all elements in m1 that are different or missing in m2
 * 
 * \param m1 the 'target' sharing_map
 * \param m2 the reference sharing map
 */
void abstract_objectt::dump_map_diff(
  std::ostream out,
  const abstract_objectt::shared_mapt &m1,
  const abstract_objectt::shared_mapt &m2)
{
  shared_mapt::delta_viewt delta_view;
  m1.get_delta_view(m2, delta_view, false);

  out << "DELTA{";
  bool first = true;
  for(auto &item : delta_view)
  {
    out << (first ? "" : ", ") << item.k << "=" << item.in_both;
    first = false;
  }
  out << "}";
}
