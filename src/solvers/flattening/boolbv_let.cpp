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
  {
    if(!bv_width.get_width_opt(value.type()).has_value())
      converted_values.emplace_back();
    else
      converted_values.push_back(convert_bv(value));
  }

  // get fresh bound symbols
  auto fresh_variables = fresh_binding(expr.binding());

  // Now assign
  for(const auto &binding : make_range(fresh_variables).zip(converted_values))
  {
    bool is_boolean = binding.first.type().id() == ID_bool;
    const auto &identifier = binding.first.get_identifier();

    // make the symbol visible
    if(is_boolean)
    {
      DATA_INVARIANT(binding.second.size() == 1, "boolean values have one bit");
      symbols[identifier] = binding.second[0];
    }
    else
      map.set_literals(identifier, binding.first.type(), binding.second);
  }

  // for renaming the bound symbols
  replace_symbolt replace_symbol;

  for(const auto &pair : make_range(variables).zip(fresh_variables))
    replace_symbol.insert(pair.first, pair.second);

  // rename the bound symbols in 'where'
  exprt where_renamed = expr.where();
  replace_symbol(where_renamed);

  // recursive call
  bvt result_bv = convert_bv(where_renamed);

  // the mapping can now be deleted
  for(const auto &entry : fresh_variables)
  {
    const auto &type = entry.type();
    if(type.id() == ID_bool)
      symbols.erase(entry.get_identifier());
    else
      map.erase_literals(entry.get_identifier(), type);
  }

  return result_bv;
}
