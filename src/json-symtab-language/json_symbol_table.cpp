/*******************************************************************\

Module: JSON symbol table deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symbol_table.h"
#include "json_symbol.h"

#include <util/exception_utils.h>
#include <util/json.h>
#include <util/symbol_table.h>

void symbol_table_from_json(const jsont &in, symbol_tablet &symbol_table)
{
  if(!in.is_object())
  {
    throw deserialization_exceptiont(
      "symbol_table_from_json: JSON input must be an object");
  }

  const json_objectt &json_object = to_json_object(in);
  const auto it = json_object.find("symbolTable");

  if(it == json_object.end())
  {
    throw deserialization_exceptiont(
      "symbol_table_from_json: JSON object must have key `symbolTable`");
  }

  if(!it->second.is_object())
  {
    throw deserialization_exceptiont(
      "symbol_table_from_json: JSON symbol table must be an object");
  }

  const json_objectt &json_symbol_table = to_json_object(it->second);

  for(const auto &pair : json_symbol_table)
  {
    const jsont &json_symbol = pair.second;

    symbolt symbol = symbol_from_json(json_symbol);

    if(symbol_table.add(symbol))
      throw deserialization_exceptiont(
        "symbol_table_from_json: duplicate symbol name `" +
        id2string(symbol.name) + "`");
  }
}
