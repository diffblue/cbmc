/*******************************************************************\

Module: Remove 'complex' data type

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

#include <util/expr_util.h>

#include "remove_complex.h"

void remove_complex(typet &);
void remove_complex(exprt &);

/*******************************************************************\

Function: complex_member

Inputs:

Outputs:

Purpose: 

\*******************************************************************/

exprt complex_member(const exprt &expr, irep_idt id)
{
  if(expr.id()==ID_struct && expr.operands().size()==2)
  {
    if(id==ID_real)
      return expr.op0();
    else if(id==ID_imag)
      return expr.op1();
    else
      assert(false);
  }
  else
  {
    assert(expr.type().id()==ID_struct);
    const struct_typet &struct_type=
      to_struct_type(expr.type());
    assert(struct_type.components().size()==2);
    return member_exprt(expr, id, struct_type.components().front().type());
  }
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(exprt &expr)
{
  if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    if(expr.op0().type().id()==ID_complex)
    {
      if(expr.type().id()==ID_complex)
      {
        // complex to complex
      }
      else
      {
        // cast complex to non-complex is (T)__real__ x
        unary_exprt tmp(
          ID_complex_real, expr.op0(), expr.op0().type().subtype());

        expr=typecast_exprt(tmp, expr.type());
      }
    }
  }

  Forall_operands(it, expr)
    remove_complex(*it);

  if(expr.type().id()==ID_complex)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div)
    {
      assert(expr.operands().size()==2);
      // do component-wise:
      // x+y -> complex(x.r+y.r,x.i+y.i)
      struct_exprt struct_expr(expr.type());
      struct_expr.operands().resize(2);

      struct_expr.op0()=
        binary_exprt(complex_member(expr.op0(), ID_real), expr.id(),
                     complex_member(expr.op1(), ID_real));

      struct_expr.op0().add_source_location()=expr.source_location();
      
      struct_expr.op1()=
        binary_exprt(complex_member(expr.op0(), ID_imag), expr.id(),
                     complex_member(expr.op1(), ID_imag));      

      struct_expr.op1().add_source_location()=expr.source_location();
      
      expr=struct_expr;
    }
    else if(expr.id()==ID_unary_minus)
    {
      assert(expr.operands().size()==1);
      // do component-wise:
      // -x -> complex(-x.r,-x.i)
      struct_exprt struct_expr(expr.type());
      struct_expr.operands().resize(2);

      struct_expr.op0()=
        unary_minus_exprt(complex_member(expr.op0(), ID_real));

      struct_expr.op0().add_source_location()=expr.source_location();
      
      struct_expr.op1()=
        unary_minus_exprt(complex_member(expr.op0(), ID_imag));

      struct_expr.op1().add_source_location()=expr.source_location();
      
      expr=struct_expr;
    }
    else if(expr.id()==ID_complex)
    {
      assert(expr.operands().size()==2);
      expr.id(ID_struct);
    }
    else if(expr.id()==ID_typecast)
    {
      assert(expr.operands().size()==1);
      typet subtype=expr.type().subtype();

      if(expr.op0().type().id()==ID_struct)
      {
        // complex to complex -- do typecast per component

        struct_exprt struct_expr(expr.type());
        struct_expr.operands().resize(2);

        struct_expr.op0()=
          typecast_exprt(complex_member(expr.op0(), ID_real), subtype);

        struct_expr.op0().add_source_location()=expr.source_location();
        
        struct_expr.op1()=
          typecast_exprt(complex_member(expr.op0(), ID_imag), subtype);

        struct_expr.op1().add_source_location()=expr.source_location();
        
        expr=struct_expr;        
      }
      else
      {
        // non-complex to complex
        struct_exprt struct_expr(expr.type());
        struct_expr.operands().resize(2);

        struct_expr.op0()=typecast_exprt(expr.op0(), subtype);
        struct_expr.op1()=gen_zero(subtype);
        struct_expr.add_source_location()=expr.source_location();
        
        expr=struct_expr;
      }
    }
  }

  if(expr.id()==ID_complex_real)
  {
    assert(expr.operands().size()==1);
    expr=complex_member(expr.op0(), ID_real);
  }
  else if(expr.id()==ID_complex_imag)
  {
    assert(expr.operands().size()==1);
    expr=complex_member(expr.op0(), ID_imag);
  }

  remove_complex(expr.type());
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(typet &type)
{
  if(type.id()==ID_struct || type.id()==ID_union)
  {
    struct_union_typet &struct_union_type=
      to_struct_union_type(type);
    for(struct_union_typet::componentst::iterator
        it=struct_union_type.components().begin();
        it!=struct_union_type.components().end();
        it++)
    {
      remove_complex(it->type());
    }
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_vector ||
          type.id()==ID_array)
  {
    remove_complex(type.subtype());
  }
  else if(type.id()==ID_complex)
  {
    remove_complex(type.subtype());
    
    // Replace by a struct with two members.
    // The real part goes first.
    struct_typet struct_type;
    struct_type.add_source_location()=type.source_location();
    struct_type.components().resize(2);
    struct_type.components()[0].type()=type.subtype();
    struct_type.components()[0].set_name(ID_real);
    struct_type.components()[1].type()=type.subtype();
    struct_type.components()[1].set_name(ID_imag);    
    
    type=struct_type;
  }
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(symbolt &symbol)
{
  remove_complex(symbol.value);
  remove_complex(symbol.type);
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(symbol_tablet &symbol_table)
{
  Forall_symbols(it, symbol_table.symbols)
    remove_complex(it->second);
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(goto_functionst::goto_functiont &goto_function)
{
  remove_complex(goto_function.type);

  Forall_goto_program_instructions(it, goto_function.body)
  {
    remove_complex(it->code);
    remove_complex(it->guard);
  }
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    remove_complex(it->second);
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_complex(symbol_table);
  remove_complex(goto_functions);
}

/*******************************************************************\

Function: remove_complex

Inputs:

Outputs:

Purpose: removes complex data type

\*******************************************************************/

void remove_complex(goto_modelt &goto_model)
{
  remove_complex(goto_model.symbol_table, goto_model.goto_functions);
}

