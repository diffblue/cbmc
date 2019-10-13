/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/range.h>
#include <util/std_expr.h>
#include <util/std_types.h>

bvt boolbvt::convert_let(const let_exprt &expr)
{
  const auto &variables = expr.variables();
  const auto &values = expr.values();

  for(auto &binding : make_range(variables).zip(values))
  {
    const bvt value_bv = convert_bv(binding.second);

    // We expect the identifiers of the bound symbols to be unique,
    // and thus, these can go straight into the symbol to literal map.
    // This property also allows us to cache any subexpressions.
    const irep_idt &id = binding.first.get_identifier();

    // the symbol shall be visible during the recursive call
    // to convert_bv
    map.set_literals(id, binding.first.type(), value_bv);
  }

  bvt result_bv=convert_bv(expr.where());

  // now remove, no longer needed
  for(auto &variable : variables)
    map.erase_literals(variable.get_identifier(), variable.type());

  return result_bv;
}
