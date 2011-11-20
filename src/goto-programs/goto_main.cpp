/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <rename.h>
#include <context.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::new_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::new_name(symbolt &symbol)
{
  // rename it
  get_new_name(symbol, ns);

  // store in context
  context.add(symbol);
}

/*******************************************************************\

Function: goto_convertt::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &goto_convertt::lookup(const irep_idt &identifier) const
{
  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
    throw "failed to find symbol "+id2string(identifier);
  return *symbol;
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  const codet &code,
  contextt &context,
  const optionst &options,
  goto_programt &dest,
  message_handlert &message_handler)
{
  goto_convertt goto_convert(context, options, message_handler);

  try
  {
    goto_convert.goto_convert(code, dest);
  }
  
  catch(int)
  {
    goto_convert.error();
  }

  catch(const char *e)
  {
    goto_convert.error(e);
  }

  catch(const std::string &e)
  {
    goto_convert.error(e);
  }

  if(goto_convert.get_error_found())
    throw 0;
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  contextt &context,
  const optionst &options,
  goto_programt &dest,
  message_handlert &message_handler)
{
  // find main symbol
  const contextt::symbolst::const_iterator s_it=
    context.symbols.find("main");
  
  if(s_it==context.symbols.end())
    throw "failed to find main symbol";
  
  const symbolt &symbol=s_it->second;
  
  ::goto_convert(to_code(symbol.value), context, options, dest, message_handler);
}
