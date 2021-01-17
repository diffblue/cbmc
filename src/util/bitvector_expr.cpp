/*******************************************************************\

Module: API to expression classes for bitvectors

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bitvector_expr.h"

#include "arith_tools.h"
#include "mathematical_types.h"

shift_exprt::shift_exprt(
  exprt _src,
  const irep_idt &_id,
  const std::size_t _distance)
  : binary_exprt(std::move(_src), _id, from_integer(_distance, integer_typet()))
{
}

extractbit_exprt::extractbit_exprt(exprt _src, const std::size_t _index)
  : binary_predicate_exprt(
      std::move(_src),
      ID_extractbit,
      from_integer(_index, integer_typet()))
{
}

extractbits_exprt::extractbits_exprt(
  exprt _src,
  const std::size_t _upper,
  const std::size_t _lower,
  typet _type)
  : expr_protectedt(ID_extractbits, std::move(_type))
{
  PRECONDITION(_upper >= _lower);
  add_to_operands(
    std::move(_src),
    from_integer(_upper, integer_typet()),
    from_integer(_lower, integer_typet()));
}
