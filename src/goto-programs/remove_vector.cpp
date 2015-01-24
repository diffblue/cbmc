/*******************************************************************\

Module: Remove 'vector' data type

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

#include <util/arith_tools.h>

#include "remove_vector.h"

void remove_vector(typet &);
void remove_vector(exprt &);

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(exprt &expr)
{
  Forall_operands(it, expr)
    remove_vector(*it);

  if(expr.type().id()==ID_vector)
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div ||
       expr.id()==ID_mod  || expr.id()==ID_bitxor ||
       expr.id()==ID_bitand || expr.id()==ID_bitor)
    {
      remove_vector(expr.type());
      array_typet array_type=to_array_type(expr.type());
      
      mp_integer dimension;
      to_integer(array_type.size(), dimension);
    
      assert(expr.operands().size()==2);
      const typet subtype=array_type.subtype();
      // do component-wise:
      // x+y -> vector(x[0]+y[0],x[1]+y[1],...)
      array_exprt array_expr(array_type);
      array_expr.operands().resize(integer2long(dimension));

      for(unsigned i=0; i<array_expr.operands().size(); i++)
      {
        exprt index=from_integer(i, array_type.size().type());
      
        array_expr.operands()[i]=
          binary_exprt(index_exprt(expr.op0(), index, subtype), expr.id(),
                       index_exprt(expr.op1(), index, subtype));
      }
      
      expr=array_expr;
    }
    else if(expr.id()==ID_unary_minus || expr.id()==ID_bitnot)
    {
      remove_vector(expr.type());
      array_typet array_type=to_array_type(expr.type());
      
      mp_integer dimension;
      to_integer(array_type.size(), dimension);
    
      assert(expr.operands().size()==1);
      const typet subtype=array_type.subtype();
      // do component-wise:
      // -x -> vector(-x[0],-x[1],...)
      array_exprt array_expr(array_type);
      array_expr.operands().resize(integer2long(dimension));

      for(unsigned i=0; i<array_expr.operands().size(); i++)
      {
        exprt index=from_integer(i, array_type.size().type());
      
        array_expr.operands()[i]=
          unary_exprt(expr.id(), index_exprt(expr.op0(), index, subtype));
      }
      
      expr=array_expr;
    }
    else if(expr.id()==ID_vector)
    {
      expr.id(ID_array);
    }
  }

  remove_vector(expr.type());
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(typet &type)
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
      remove_vector(it->type());
    }
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_complex ||
          type.id()==ID_array)
  {
    remove_vector(type.subtype());
  }
  else if(type.id()==ID_vector)
  {
    vector_typet &vector_type=to_vector_type(type);
  
    remove_vector(type.subtype());
    
    // Replace by an array with appropriate number of members.
    array_typet array_type(vector_type.subtype(), vector_type.size());
    array_type.add_source_location()=type.source_location();
    type=array_type;
  }
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(symbolt &symbol)
{
  remove_vector(symbol.value);
  remove_vector(symbol.type);
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(symbol_tablet &symbol_table)
{
  Forall_symbols(it, symbol_table.symbols)
    remove_vector(it->second);
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(goto_functionst::goto_functiont &goto_function)
{
  remove_vector(goto_function.type);

  Forall_goto_program_instructions(it, goto_function.body)
  {
    remove_vector(it->code);
    remove_vector(it->guard);
  }
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    remove_vector(it->second);
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_vector(symbol_table);
  remove_vector(goto_functions);
}

/*******************************************************************\

Function: remove_vector

Inputs:

Outputs:

Purpose: removes vector data type

\*******************************************************************/

void remove_vector(goto_modelt &goto_model)
{
  remove_vector(goto_model.symbol_table, goto_model.goto_functions);
}

