/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/range.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

bvt boolbvt::convert_let(const let_exprt &expr)
{
  const auto &variables = expr.variables();
  const auto &values = expr.values();

  DATA_INVARIANT(
    expr.type() == expr.where().type(),
    "let must have the type of the 'where' operand");

  // Check the types.
  for(auto &binding : make_range(variables).zip(values))
  {
    DATA_INVARIANT(
      binding.first.type() == binding.second.type(),
      "let value must have the type of the let symbol");
  }

  // A let expression can bind multiple symbols simultaneously.
  // This is a 'concurrent' binding, i.e., the symbols are not yet
  // visible when evaluating the values. SMT-LIB also has this
  // semantics. We therefore first convert all values,
  // and only then assign them.
  std::vector<bvt> converted_values;
  converted_values.reserve(variables.size());

  for(auto &value : values)
    converted_values.push_back(convert_bv(value));

  scope_counter++;

  // for renaming the bound symbols
  replace_symbolt replace_symbol;

  // Now assign
  for(const auto &binding : make_range(variables).zip(converted_values))
  {
    bool is_boolean = binding.first.type().id() == ID_bool;
    const auto &old_identifier = binding.first.get_identifier();

    // produce a new identifier
    const irep_idt new_identifier =
      "boolbvt::scope::" + std::to_string(scope_counter) +
      "::" + id2string(old_identifier);

    // make the symbol visible
    if(is_boolean)
    {
      DATA_INVARIANT(binding.second.size() == 1, "boolean values have one bit");
      symbols[new_identifier] = binding.second[0];
    }
    else
      map.set_literals(new_identifier, binding.first.type(), binding.second);

    // remember the renaming
    replace_symbol.insert(
      binding.first, symbol_exprt(new_identifier, binding.first.type()));
  }

  // rename the bound symbols in 'where'
  exprt where_renamed = expr.where();
  replace_symbol(where_renamed);

  // recursive call
  bvt result_bv = convert_bv(where_renamed);

  // the mapping can now be deleted
  for(const auto &entry : replace_symbol.get_expr_map())
  {
    const auto &new_symbol = to_symbol_expr(entry.second);
    const auto &type = new_symbol.type();
    if(type.id() == ID_bool)
      symbols.erase(new_symbol.get_identifier());
    else
      map.erase_literals(new_symbol.get_identifier(), type);
  }

  return result_bv;
}
