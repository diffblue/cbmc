/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/type_eq.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::find_constructor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::find_constructor(
  const typet &start_dest_type,
  exprt &constructor_expr)
{
  constructor_expr.make_nil();

  locationt location=start_dest_type.location();
  typet dest_type(start_dest_type);
  follow_symbol(dest_type);

  if(dest_type.id()!=ID_struct)
    return;

  const struct_typet::componentst &components=
    to_struct_type(dest_type).components();

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const struct_typet::componentt &component=*it;
    const typet &type=component.type();

    if(type.find(ID_return_type).id()==ID_constructor)
    {
      const irept::subt &arguments=
        type.find(ID_arguments).get_sub();

      namespacet ns(symbol_table);

      if(arguments.size()==1)
      {
        const exprt &argument=(exprt &)arguments.front();
        const typet &arg_type=argument.type();

        if(arg_type.id()==ID_pointer &&
           type_eq(arg_type.subtype(), dest_type, ns))
        {
          // found!
          const irep_idt &identifier=
            component.get(ID_name);

          if(identifier=="")
            throw "constructor without identifier";

          constructor_expr=exprt(ID_symbol, type);
          constructor_expr.set(ID_identifier, identifier);
          constructor_expr.location()=location;
          return;
        }
      }
    }
  }
}
