/*******************************************************************\

Module: GOTO-DIFF Base Class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Base Class

#include "goto_diff.h"

#include <util/json_expr.h>

std::ostream &goto_difft::output_functions(std::ostream &out) const
{
  namespacet ns1(goto_model1.symbol_table);
  namespacet ns2(goto_model2.symbol_table);
  switch(ui)
  {
    case ui_message_handlert::uit::PLAIN:
    {
      out << "total number of functions: " << total_functions_count << "\n";
      out << "new functions:\n";
      for(irep_id_sett::const_iterator it=new_functions.begin();
          it!=new_functions.end(); ++it)
      {
        const symbolt &symbol = ns2.lookup(*it);
        out << "  " << symbol.location.get_file() << ": " << *it << "\n";
      }

      out << "modified functions:\n";
      for(irep_id_sett::const_iterator it=modified_functions.begin();
          it!=modified_functions.end(); ++it)
      {
        const symbolt &symbol = ns2.lookup(*it);
        out << "  " << symbol.location.get_file() << ": " << *it << "\n";
      }

      out << "deleted functions:\n";
      for(irep_id_sett::const_iterator it=deleted_functions.begin();
          it!=deleted_functions.end(); ++it)
      {
        const symbolt &symbol = ns1.lookup(*it);
        out << "  " << symbol.location.get_file() << ": " << *it << "\n";
      }
      break;
    }
    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["totalNumberOfFunctions"]=
        json_stringt(std::to_string(total_functions_count));
      convert_function_group
        (json_result["newFunctions"].make_array(), new_functions);
      convert_function_group(
        json_result["modifiedFunctions"].make_array(), modified_functions);
      convert_function_group(
        json_result["deletedFunctions"].make_array(), deleted_functions);
      out << ",\n" << json_result;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      out << "not supported yet";
    }
  }
  return out;
}

void goto_difft::convert_function_group(
  json_arrayt &result,
  const irep_id_sett &function_group) const
{
  for(irep_id_sett::const_iterator it=function_group.begin();
      it!=function_group.end(); ++it)
  {
    convert_function(result.push_back(jsont()).make_object(), *it);
  }
}

void goto_difft::convert_function(
  json_objectt &result,
  const irep_idt &function_name) const
{
  // the function may be in goto_model1 or goto_model2
  if(
    goto_model1.goto_functions.function_map.find(function_name) !=
    goto_model1.goto_functions.function_map.end())
  {
    const symbolt &symbol =
      namespacet(goto_model1.symbol_table).lookup(function_name);
    result["sourceLocation"] = json(symbol.location);
  }
  else if(
    goto_model2.goto_functions.function_map.find(function_name) !=
    goto_model2.goto_functions.function_map.end())
  {
    const symbolt &symbol =
      namespacet(goto_model2.symbol_table).lookup(function_name);
    result["sourceLocation"] = json(symbol.location);
  }
  result["name"]=json_stringt(id2string(function_name));
}
