/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "pointer_arithmetic.h"

#include <util/arith_tools.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

pointer_arithmetict::pointer_arithmetict(const exprt &src)
{
  pointer.make_nil();
  offset.make_nil();
  read(src);
}

void pointer_arithmetict::read(const exprt &src)
{
  if(src.id()==ID_plus)
  {
    for(const auto &op : src.operands())
    {
      if(op.type().id() == ID_pointer)
        read(op);
      else
        add_to_offset(op);
    }
  }
  else if(src.id()==ID_minus)
  {
    auto const &minus_src = to_minus_expr(src);
    read(minus_src.op0());
    const unary_minus_exprt unary_minus(
      minus_src.op1(), minus_src.op1().type());
    add_to_offset(unary_minus);
  }
  else if(src.id()==ID_address_of)
  {
    auto const &address_of_src = to_address_of_expr(src);
    if(address_of_src.op().id() == ID_index)
    {
      const index_exprt &index_expr = to_index_expr(address_of_src.op());

      if(index_expr.index().is_zero())
        make_pointer(address_of_src);
      else
      {
        add_to_offset(index_expr.index());
        // produce &x[0] + i instead of &x[i]
        auto new_address_of_src = address_of_src;
        to_index_expr(new_address_of_src.op()).index() =
          from_integer(0, index_expr.index().type());
        make_pointer(new_address_of_src);
      }
    }
    else
      make_pointer(address_of_src);
  }
  else
    make_pointer(src);
}

void pointer_arithmetict::add_to_offset(const exprt &src)
{
  if(offset.is_nil())
    offset=src;
  else if(offset.id()==ID_plus)
    offset.copy_to_operands(src);
  else
  {
    offset =
      plus_exprt(offset, typecast_exprt::conditional_cast(src, offset.type()));
  }
}

void pointer_arithmetict::make_pointer(const exprt &src)
{
  if(pointer.is_nil())
    pointer=src;
  else
    add_to_offset(src);
}
