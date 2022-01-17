/*******************************************************************\

Module: API to expression classes that are internal to the C frontend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_expr.h"

#include <util/arith_tools.h>

shuffle_vector_exprt::shuffle_vector_exprt(
  exprt vector1,
  optionalt<exprt> vector2,
  exprt::operandst indices)
  : multi_ary_exprt(
      ID_shuffle_vector,
      {std::move(vector1), nil_exprt{}, exprt{}},
      typet{})
{
  if(vector2.has_value())
    op1() = std::move(*vector2);

  const vector_typet &vt = to_vector_type(op0().type());
  type() = vector_typet{vt.element_type(),
                        from_integer(indices.size(), vt.size().type())};

  op2().operands().swap(indices);
}

vector_exprt shuffle_vector_exprt::lower() const
{
  PRECONDITION(
    !has_two_input_vectors() || vector1().type() == vector2().type());

  if(indices().empty())
    return vector_exprt{exprt::operandst{}, type()};

  auto input_size =
    numeric_cast<mp_integer>(to_vector_type(vector1().type()).size());
  CHECK_RETURN(input_size.has_value());

  exprt::operandst operands;
  operands.reserve(indices().size());

  for(const exprt &index : indices())
  {
    if(has_two_input_vectors())
    {
      operands.push_back(if_exprt{
        binary_predicate_exprt{
          index, ID_lt, from_integer(*input_size, index.type())},
        index_exprt{vector1(), index},
        index_exprt{
          vector2(),
          minus_exprt{index, from_integer(*input_size, index.type())}}});
    }
    else
      operands.push_back(index_exprt{vector1(), index});
  }

  return vector_exprt{std::move(operands), type()};
}
