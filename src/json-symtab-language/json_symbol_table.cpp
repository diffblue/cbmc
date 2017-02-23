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
  if(!in.is_array())
    throw deserialization_exceptiont(
      "symbol_table_from_json: JSON input must be an array");
  for(const auto &js_symbol : in.array)
  {
    symbolt deserialized = symbol_from_json(js_symbol);
    if(symbol_table.add(deserialized))
      throw deserialization_exceptiont(
        "symbol_table_from_json: duplicate symbol name '" +
        id2string(deserialized.name) + "'");
  }
}
