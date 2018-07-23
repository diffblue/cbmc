/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history

#include "ai_history.h"

bool history_ptrt::operator<(const history_ptrt &op) const
{
  return *p < *op.p;
}

bool history_ptrt::operator==(const history_ptrt &op) const
{
  return *p == *op.p;
}

jsont ai_history_baset::output_json(void) const
{
  std::ostringstream out;
  output(out);
  json_stringt json(out.str());
  return json;
}

xmlt ai_history_baset::output_xml(void) const
{
  std::ostringstream out;
  output(out);
  xmlt xml("abstract_state");
  xml.data = out.str();
  return xml;
}
