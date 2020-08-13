/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history

#include "ai_history.h"

jsont ai_history_baset::output_json(void) const
{
  std::ostringstream out;
  output(out);
  json_stringt json(out.str());
  return std::move(json);
}

xmlt ai_history_baset::output_xml(void) const
{
  std::ostringstream out;
  output(out);
  xmlt xml("history");
  xml.data = out.str();
  return xml;
}

const ai_history_baset::trace_ptrt ai_history_baset::no_caller_history =
  nullptr;
