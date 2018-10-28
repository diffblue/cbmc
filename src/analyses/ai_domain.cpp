/*******************************************************************\

Module: Abstract Interpretation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract Interpretation Domain

#include "ai_domain.h"

#include <util/simplify_expr.h>

jsont ai_domain_baset::output_json(const ai_baset &ai, const namespacet &ns)
  const
{
  std::ostringstream out;
  output(out, ai, ns);
  json_stringt json(out.str());
  return std::move(json);
}

xmlt ai_domain_baset::output_xml(const ai_baset &ai, const namespacet &ns) const
{
  std::ostringstream out;
  output(out, ai, ns);
  xmlt xml("abstract_state");
  xml.data = out.str();
  return xml;
}

/// Use the information in the domain to simplify the expression on the LHS of
/// an assignment. This for example won't simplify symbols to their values, but
/// does simplify indices in arrays, members of structs and dereferencing of
/// pointers
/// \param condition: the expression to simplify
/// \param ns: the namespace
/// \return True if condition did not change. False otherwise. condition will be
///   updated with the simplified condition if it has worked
bool ai_domain_baset::ai_simplify_lhs(exprt &condition, const namespacet &ns)
  const
{
  // Care must be taken here to give something that is still writable
  if(condition.id() == ID_index)
  {
    index_exprt ie = to_index_expr(condition);
    bool no_simplification = ai_simplify(ie.index(), ns);
    if(!no_simplification)
      condition = simplify_expr(ie, ns);

    return no_simplification;
  }
  else if(condition.id() == ID_dereference)
  {
    dereference_exprt de = to_dereference_expr(condition);
    bool no_simplification = ai_simplify(de.pointer(), ns);
    if(!no_simplification)
      condition = simplify_expr(de, ns); // So *(&x) -> x

    return no_simplification;
  }
  else if(condition.id() == ID_member)
  {
    member_exprt me = to_member_expr(condition);
    // Since simplify_ai_lhs is required to return an addressable object
    // (so remains a valid left hand side), to simplify
    // `(something_simplifiable).b` we require that `something_simplifiable`
    // must also be addressable
    bool no_simplification = ai_simplify_lhs(me.compound(), ns);
    if(!no_simplification)
      condition = simplify_expr(me, ns);

    return no_simplification;
  }
  else
    return true;
}
