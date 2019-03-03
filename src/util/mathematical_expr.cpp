/*******************************************************************\

Module: API to expression classes for 'mathematical' expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "mathematical_expr.h"
#include "mathematical_types.h"

function_application_exprt::function_application_exprt(
  const symbol_exprt &_function,
  argumentst _arguments)
  : binary_exprt(
      _function,
      ID_function_application,
      multi_ary_exprt(irep_idt(), std::move(_arguments), typet()),
      to_mathematical_function_type(_function.type()).codomain())
{
  const auto &domain = to_mathematical_function_type(_function.type()).domain();
  PRECONDITION(domain.size() == arguments().size());
}
