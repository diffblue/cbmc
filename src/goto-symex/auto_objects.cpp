/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <prefix.h>
#include <cprover_prefix.h>
#include <context.h>
#include <std_expr.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::make_auto_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_symext::make_auto_object(const typet &type)
{
  dynamic_counter++;
  
  // produce auto-object symbol
  symbolt symbol;

  symbol.base_name="auto_object"+i2string(dynamic_counter);
  symbol.name="symex::"+id2string(symbol.base_name);
  symbol.lvalue=true;
  symbol.type=type;
  symbol.mode=ID_C;

  new_context.add(symbol);

  return symbol_exprt(symbol.name, symbol.type);
}

/*******************************************************************\

Function: goto_symext::initialize_auto_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::initialize_auto_object(
  const exprt &expr,
  statet &state)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &t=ns.follow(it->type());
      if(t.id()==ID_pointer)
      {
        const typet &subtype=ns.follow(t.subtype());
        
        // we don't like function pointers and
        // we don't like void *
        if(subtype.id()!=ID_code &&
           subtype.id()!=ID_empty)
        {
          member_exprt member_expr;
          member_expr.struct_op()=expr;
          member_expr.set_component_name(it->get_name());
          member_expr.type()=it->type();
          
          address_of_exprt rhs=
            address_of_exprt(make_auto_object(t.subtype()));

          code_assignt assignment(member_expr, rhs);
          symex_assign(state, assignment);
        }
      }
    }
  }
}

/*******************************************************************\

Function: goto_symext::trigger_auto_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::trigger_auto_object(
  const exprt &expr,
  statet &state)
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get_identifier();
    
    const symbolt &symbol=
      ns.lookup(state.get_original_name(identifier));
      
    if(has_prefix(id2string(symbol.base_name), "auto_object"))
    {
      // done already?
      if(state.level2.current_names.find(identifier)==
         state.level2.current_names.end())
      {
        initialize_auto_object(expr, state);
      }
    }
  }

  // recursive call
  forall_operands(it, expr)
    trigger_auto_object(*it, state);
}
