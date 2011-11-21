/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"
#include "expr_util.h"

#include "pointer_arithmetic.h"

/*******************************************************************\

Function: pointer_arithmetict::pointer_arithmetict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

pointer_arithmetict::pointer_arithmetict(const exprt &src)
{
  pointer.make_nil();
  offset.make_nil();
  read(src);
}

/*******************************************************************\

Function: pointer_arithmetict::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_arithmetict::read(const exprt &src)
{
  if(src.id()==ID_plus)
  {
    forall_operands(it, src)
    {
      if(it->type().id()==ID_pointer)
        read(*it);
      else
        add_to_offset(*it);
    }
  }
  else if(src.id()==ID_minus)
  {
    assert(src.operands().size()==2);
    read(src.op0());
    exprt o=unary_minus_exprt(src.op1(), src.op1().type());
    add_to_offset(o);
  }
  else if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    if(src.op0().id()==ID_index)
    {
      const index_exprt &index_expr=
        to_index_expr(src.op0());

      if(index_expr.index().is_zero())
        make_pointer(src);
      else
      {
        add_to_offset(index_expr.index());
        // produce &x[0] + i instead of &x[i]
        exprt new_src=src;
        new_src.op0().op1()=gen_zero(index_expr.index().type());
        make_pointer(new_src);
      }
    }
    else
      make_pointer(src);
  }
  else
    make_pointer(src);
}

/*******************************************************************\

Function: pointer_arithmetict::add_to_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_arithmetict::add_to_offset(const exprt &src)
{
  if(offset.is_nil())
    offset=src;
  else if(offset.id()==ID_plus)
    offset.copy_to_operands(src);
  else
  {
    exprt new_offset=plus_exprt(offset, src);

    if(new_offset.op1().type()!=offset.type())
      new_offset.op1().make_typecast(offset.type());
      
    offset=new_offset;
  }
}

/*******************************************************************\

Function: pointer_arithmetict::make_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void pointer_arithmetict::make_pointer(const exprt &src)
{
  if(pointer.is_nil())
    pointer=src;
  else
    add_to_offset(src);
}

