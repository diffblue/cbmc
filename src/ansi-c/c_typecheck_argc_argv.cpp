/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <expr_util.h>

#include "c_typecheck_base.h"

/*******************************************************************\

Function: c_typecheck_baset::add_argc_argv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::add_argc_argv(const symbolt &main_symbol)
{
  const irept &arguments=
    main_symbol.type.find(ID_arguments);

  if(arguments.get_sub().size()==0)
    return;

  if(arguments.get_sub().size()!=2 &&
     arguments.get_sub().size()!=3)
  {
    err_location(main_symbol.location);
    throw "main expected to have no or two or three arguments";
  }

  symbolt *argc_new_symbol;
  
  const exprt &op0=static_cast<const exprt &>(arguments.get_sub()[0]);
  const exprt &op1=static_cast<const exprt &>(arguments.get_sub()[1]);

  {
    symbolt argc_symbol;

    argc_symbol.base_name="argc";
    argc_symbol.name="c::argc'";
    argc_symbol.type=op0.type();
    argc_symbol.static_lifetime=true;
    argc_symbol.lvalue=true;

    if(argc_symbol.type.id()!=ID_signedbv &&
       argc_symbol.type.id()!=ID_unsignedbv)
    {
      err_location(main_symbol.location);
      str << "argc argument expected to be integer type, but got `"
          << to_string(argc_symbol.type) << "'";
      throw 0;
    }

    move_symbol(argc_symbol, argc_new_symbol);
  }

  {
    if(op1.type().id()!=ID_pointer ||
       op1.type().subtype().id()!=ID_pointer)
    {
      err_location(main_symbol.location);
      str << "argv argument expected to be pointer-to-pointer type, "
             "but got `"
          << to_string(op1.type()) << "'";
      throw 0;
    }

    // we make the type of this thing an array of pointers
    typet argv_type=array_typet();
    argv_type.subtype()=op1.type().subtype();

    // need to add one to the size -- the array is terminated
    // with NULL
    exprt one_expr=from_integer(1, argc_new_symbol->type);
    
    exprt size_expr(ID_plus, argc_new_symbol->type);
    size_expr.copy_to_operands(symbol_expr(*argc_new_symbol), one_expr);
    argv_type.add(ID_size).swap(size_expr);

    symbolt argv_symbol;

    argv_symbol.base_name="argv";
    argv_symbol.name="c::argv'";
    argv_symbol.type=argv_type;
    argv_symbol.static_lifetime=true;
    argv_symbol.lvalue=true;

    symbolt *argv_new_symbol;
    move_symbol(argv_symbol, argv_new_symbol);
  }
  
  if(arguments.get_sub().size()==3)
  {    
    symbolt envp_symbol;    
    envp_symbol.base_name="envp";
    envp_symbol.name="c::envp'";
    envp_symbol.type=(static_cast<const exprt&>(arguments.get_sub()[2])).type();
    envp_symbol.static_lifetime=true;
    
    symbolt envp_size_symbol, *envp_new_size_symbol;
    envp_size_symbol.base_name="envp_size";
    envp_size_symbol.name="c::envp_size'";
    envp_size_symbol.type=op0.type(); // same type as argc!
    envp_size_symbol.static_lifetime=true;    
    move_symbol(envp_size_symbol, envp_new_size_symbol);        

    if(envp_symbol.type.id()!=ID_pointer)
    {
      err_location(main_symbol.location);
      str << "envp argument expected to be pointer type, but got `"
          << to_string(envp_symbol.type) << "'";
      throw 0;
    }
    
    exprt size_expr = symbol_expr(*envp_new_size_symbol);

    envp_symbol.type.id(ID_array);
    envp_symbol.type.add(ID_size).swap(size_expr);
    
    symbolt *envp_new_symbol;
    move_symbol(envp_symbol, envp_new_symbol);
  }
}
