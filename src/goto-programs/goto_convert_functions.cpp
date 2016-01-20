/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <cassert>

#include <util/base_type.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/prefix.h>

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
  symbol_tablet &_symbol_table,
  goto_functionst &_functions,
  message_handlert &_message_handler):
  goto_convertt(_symbol_table, _message_handler),
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

  forall_symbols(it, symbol_table.symbols)
  {
    if(!it->second.is_type &&
       it->second.type.id()==ID_code &&
       (it->second.mode==ID_C || it->second.mode==ID_cpp))
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
  Forall_symbols(it, symbol_table.symbols)
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
  const source_locationt &source_location)
{
  #if 0
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_return())
    return; // not needed, we have one already
    
  // see if we have an unconditional goto at the end
  if(!f.body.instructions.empty() &&
     f.body.instructions.back().is_goto() &&
     f.body.instructions.back().guard.is_true())
    return;
  #else

  if(!f.body.instructions.empty())
  {
    goto_programt::const_targett last_instruction=
      f.body.instructions.end();
    last_instruction--;

    while(true)
    {
      // unconditional goto, say from while(1)?
      if(last_instruction->is_goto() &&
         last_instruction->guard.is_true())
        return;

      // return?        
      if(last_instruction->is_return())
        return;

      // advance if it's a 'dead' without branch target
      if(last_instruction->is_dead() &&
         last_instruction!=f.body.instructions.begin() &&
         !last_instruction->is_target())
        last_instruction--;
      else
        break; // give up
    }
  }
  
  #endif

  goto_programt::targett t=f.body.add_instruction();
  t->make_return();
  t->code=code_returnt();
  t->source_location=source_location;

  side_effect_expr_nondett rhs(f.type.return_type());
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
  if(!f.body.instructions.empty()) return; // already converted
  f.body_available=
    symbol.value.is_not_nil() &&
    symbol.value.id()!="compiled"; /* goto_inline may have removed the body */

  if(!f.body_available) return;
  
  if(symbol.value.id()!=ID_code)
  {
    err_location(symbol.value);
    throw "got invalid code for function `"+id2string(identifier)+"'";
  }
  
  const codet &code=to_code(symbol.value);
  
  source_locationt end_location;

  if(code.get_statement()==ID_block)
    end_location=to_code_block(code).end_location();
  else
    end_location.make_nil();

  goto_programt tmp_end_function;
  goto_programt::targett end_function=tmp_end_function.add_instruction();
  end_function->type=END_FUNCTION;
  end_function->source_location=end_location;
  end_function->code.set(ID_identifier, identifier);

  targets=targetst();
  targets.set_return(end_function);
  targets.has_return_value=
    f.type.return_type().id()!=ID_empty &&
    f.type.return_type().id()!=ID_constructor &&
    f.type.return_type().id()!=ID_destructor;

  goto_convert_rec(code, f.body);
  
  // add non-det return value, if needed
  if(targets.has_return_value)
    add_return(f, end_location);
      
  // handle SV-COMP's __VERIFIER_atomic_
  if(!f.body.instructions.empty() &&
      has_prefix(id2string(identifier), "__VERIFIER_atomic_"))
  {
    goto_programt::instructiont a_begin;
    a_begin.make_atomic_begin();
    a_begin.source_location=f.body.instructions.front().source_location;
    f.body.insert_before_swap(f.body.instructions.begin(), a_begin);

    goto_programt::targett a_end=f.body.add_instruction();
    a_end->make_atomic_end();
    a_end->source_location=end_location;

    Forall_goto_program_instructions(i_it, f.body)
    {
      if(i_it->is_goto() && i_it->get_target()->is_end_function())
        i_it->set_target(a_end);
    }
  }

  // add "end of function"
  f.body.destructive_append(tmp_end_function);

  // do function tags
  Forall_goto_program_instructions(i_it, f.body)
    i_it->function=identifier;
  
  // remove_skip depends on the target numbers
  f.body.compute_target_numbers();

  remove_skip(f.body);

  f.body.update();

  if(hide(f.body))
    f.make_hidden();
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  symbol_tablet &symbol_table,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  goto_convert(symbol_table, goto_model.goto_functions, message_handler);
  goto_model.symbol_table.swap(symbol_table);
}

/*******************************************************************\

Function: goto_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convert(
  symbol_tablet &symbol_table,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  goto_convert_functionst goto_convert_functions(
    symbol_table, functions, message_handler);
  
  try
  {  
    goto_convert_functions.goto_convert();
  }

  catch(int)
  {
    goto_convert_functions.error_msg();
  }

  catch(const char *e)
  {
    goto_convert_functions.str << e;
    goto_convert_functions.error_msg();
  }

  catch(const std::string &e)
  {
    goto_convert_functions.str << e;
    goto_convert_functions.error_msg();
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
  symbol_tablet &symbol_table,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  goto_convert_functionst goto_convert_functions(
    symbol_table, functions, message_handler);
  
  try
  {  
    goto_convert_functions.convert_function(identifier);
  }

  catch(int)
  {
    goto_convert_functions.error_msg();
  }

  catch(const char *e)
  {
    goto_convert_functions.str << e;
    goto_convert_functions.error_msg(e);
  }

  catch(const std::string &e)
  {
    goto_convert_functions.str << e;
    goto_convert_functions.error_msg(e);
  }

  if(goto_convert_functions.get_error_found())
    throw 0;
}


