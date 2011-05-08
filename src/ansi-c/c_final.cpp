/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <message_stream.h>
#include <namespace.h>
#include <std_types.h>
#include <replace_symbol.h>
#include <replace_expr.h>

#include "c_types.h"
#include "c_final.h"
#include "cprover_library.h"

/*******************************************************************\

Function: c_final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void c_finalize_expression(
  const contextt &context,
  exprt &expr,
  message_handlert &message_handler)
{
  if(expr.id()==ID_symbol)
  {
    if(expr.type().id()==ID_incomplete_array)
    {
      symbolst::const_iterator it=
        context.symbols.find(expr.get(ID_identifier));

      if(it==context.symbols.end())
      {
        message_streamt message_stream(message_handler);
        message_stream.str
          << "c_finalize_expression: failed to find symbol `"
          << expr.get("identifier") << "'";
        message_stream.error();
        throw 0;
      }
      
      const symbolt &symbol=it->second;

      if(symbol.type.id()==ID_array)
        expr.type()=symbol.type;
      else if(symbol.type.id()==ID_incomplete_array)
      {
        message_streamt message_stream(message_handler);
        message_stream.err_location(symbol.location);
        message_stream.str
          << "symbol `" << symbol.display_name()
          << "' has incomplete type";
        message_stream.error();
        throw 0;            
      }
      else
      {
        message_streamt message_stream(message_handler);
        message_stream.err_location(symbol.location);
        message_stream.str
          << "symbol `" << symbol.display_name()
          << "' has an unexpected type";
        message_stream.error();
        throw 0;      
      }
    }
  }

  if(expr.has_operands())
    Forall_operands(it, expr)
      c_finalize_expression(context, *it, message_handler);
}
#endif

/*******************************************************************\

Function: add_external_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool add_external_objects(
  contextt &context, 
  message_handlert &message_handler)
{
  namespacet ns(context);
    
  replace_mapt replace_map;
  
  Forall_symbols(it, context.symbols)
  {
    symbolt &symbol=it->second;    
    const typet &final_type=ns.follow(symbol.type);

    if(symbol.mode==ID_C && 
       symbol.is_extern && !symbol.is_type)
    {      
      if(final_type.id()==ID_incomplete_array)
      {
        // all arrays get a symbol-type
        // (see c_typecheck_baset::typecheck_new_symbol)
        assert(symbol.type.id()==ID_symbol);
        
        #if 0
        message_streamt message_stream(message_handler);
        message_stream.err_location(symbol.location);
        message_stream.str
          << "symbol `" << symbol.display_name()
          << "' is declared extern but never defined. "
          << "The object will be modeled as an array of infinite size.";
        message_stream.warning();
        #endif
        
        array_typet new_type;
        new_type.subtype()=final_type.subtype();
        new_type.size()=exprt(ID_infinity, index_type());
                
        const irep_idt &ident=symbol.type.get(ID_identifier);
        contextt::symbolst::iterator fit=context.symbols.find(ident);
        
        if(fit==context.symbols.end())
          throw std::string("symbol not found: `")+ident.as_string()+"'";
        
        // set the new type
        fit->second.type=new_type;
      }      
    }
  }
    
  return false;
}

/*******************************************************************\

Function: c_final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_final(contextt &context, message_handlert &message_handler)
{
  add_cprover_library(context, message_handler);
  add_external_objects(context, message_handler);

  return false;
}
