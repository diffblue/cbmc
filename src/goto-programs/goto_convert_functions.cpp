/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <assert.h>

#include <base_type.h>
#include <std_code.h>
#include <context.h>

#include "goto_convert_functions.h"
#include "goto_inline.h"
#include "remove_skip.h"

/*******************************************************************\

Function: goto_convert_functionst::goto_convert_functionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_convert_functionst::goto_convert_functionst(
  contextt &_context,
  const optionst &_options,
  goto_functionst &_functions,
  message_handlert &_message_handler):
  goto_convertt(_context, _options, _message_handler),
  functions(_functions)
{
}
  
/*******************************************************************\

Function: goto_convert_functionst::~goto_convert_functionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_convert_functionst::~goto_convert_functionst()
{
}

/*******************************************************************\

Function: goto_convert_functionst::goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert_functionst::goto_convert()
{
  // warning! hash-table iterators are not stable

  typedef std::list<irep_idt> symbol_listt;
  symbol_listt symbol_list;

  forall_symbols(it, context.symbols)
  {
    if(!it->second.is_type &&
       it->second.type.id()==ID_code)
      symbol_list.push_back(it->first);
  }
  
  for(symbol_listt::const_iterator
      it=symbol_list.begin();
      it!=symbol_list.end();
      it++)
  {
    convert_function(*it);
  }
  
  functions.compute_location_numbers();

  // this removes the parse tree of the bodies from memory
  #if 0
  Forall_symbols(it, context.symbols)
  {
    if(!it->second.is_type &&
       it->second.type.id()==ID_code &&
       it->second.value.is_not_nil())
      it->second.value=codet();
  }
  #endif
}

/*******************************************************************\

Function: goto_convert_functionst::hide

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_convert_functionst::hide(const goto_programt &goto_program)
{
  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    for(goto_programt::instructiont::labelst::const_iterator
        l_it=i_it->labels.begin();
        l_it!=i_it->labels.end();
        l_it++)
    {
      if(*l_it=="__CPROVER_HIDE")
        return true;
    }
  }
  
  return false;
}

/*******************************************************************\

Function: goto_convert_functionst::add_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert_functionst::add_return(
  goto_functionst::goto_functiont &f,
  const locationt &location)
{
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_return())
    return; // not needed, we have one already
    
  // see if we have an unconditional goto at the end
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_goto() &&
     f.body.instructions.back().guard.is_true())
    return;

  goto_programt::targett t=f.body.add_instruction();
  t->make_return();
  t->code=code_returnt();
  t->location=location;

  exprt rhs=exprt(ID_sideeffect, f.type.return_type());
  rhs.set(ID_statement, ID_nondet);
  t->code.move_to_operands(rhs);
}

/*******************************************************************\

Function: goto_convert_functionst::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert_functionst::convert_function(const irep_idt &identifier)
{
  const symbolt &symbol=ns.lookup(identifier);
  goto_functionst::goto_functiont &f=functions.function_map[identifier];
  
  // make tmp variables local to function
  tmp_symbol_prefix=id2string(symbol.name)+"::$tmp::";
  temporary_counter=0;
  
  f.type=to_code_type(symbol.type);
  f.body_available=symbol.value.is_not_nil();

  if(!f.body_available) return;
  
  if(symbol.value.id()!=ID_code)
  {
    err_location(symbol.value);
    throw "got invalid code for function `"+id2string(identifier)+"'";
  }
  
  const codet &code=to_code(symbol.value);
  
  locationt end_location;

  if(code.get_statement()==ID_block)
    end_location=static_cast<const locationt &>(
      code.find("#end_location"));
  else
    end_location.make_nil();

  targets=targetst();
  targets.return_set=true;
  targets.return_value=
    f.type.return_type().id()!=ID_empty &&
    f.type.return_type().id()!=ID_constructor &&
    f.type.return_type().id()!=ID_destructor;

  goto_convert_rec(code, f.body);
  
  // add non-det return value, if needed
  if(targets.return_value)
    add_return(f, end_location);
      
  // add "end of function"
  goto_programt::targett t=f.body.add_instruction();
  t->type=END_FUNCTION;
  t->location=end_location;
  t->code.set(ID_identifier, identifier);

  // do function tags
  Forall_goto_program_instructions(i_it, f.body)
    i_it->function=identifier;
  
  // remove_skip depends on the target numbers
  f.body.compute_target_numbers();

  remove_skip(f.body);

  f.body.update();

  if(hide(f.body))
    f.type.set("#hide", true);
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
  goto_functionst &functions,
  message_handlert &message_handler)
{
  goto_convert_functionst goto_convert_functions(
    context, options, functions, message_handler);
  
  try
  {  
    goto_convert_functions.goto_convert();
  }

  catch(int)
  {
    goto_convert_functions.error();
  }

  catch(const char *e)
  {
    goto_convert_functions.error(e);
  }

  catch(const std::string &e)
  {
    goto_convert_functions.error(e);
  }

  if(goto_convert_functions.get_error_found())
    throw 0;
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  const irep_idt &identifier,
  contextt &context,
  const optionst &options,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  goto_convert_functionst goto_convert_functions(
    context, options, functions, message_handler);
  
  try
  {  
    goto_convert_functions.convert_function(identifier);
  }

  catch(int)
  {
    goto_convert_functions.error();
  }

  catch(const char *e)
  {
    goto_convert_functions.error(e);
  }

  catch(const std::string &e)
  {
    goto_convert_functions.error(e);
  }

  if(goto_convert_functions.get_error_found())
    throw 0;
}


