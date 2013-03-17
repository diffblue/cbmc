/*******************************************************************\

Module: Function Entering and Exiting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cprover_prefix.h>
#include <prefix.h>
#include <std_expr.h>
#include <expr_util.h>

#include <ansi-c/c_types.h>
#include <ansi-c/string_constant.h>

#include "function.h"

/*******************************************************************\

Function: function_to_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

code_function_callt function_to_call(
  symbol_tablet &symbol_table,
  const irep_idt &id,
  const irep_idt &argument)
{
  // already there?
  
  irep_idt full_id="c::"+id2string(id);

  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(full_id);
    
  if(s_it==symbol_table.symbols.end())
  {
    // not there
    pointer_typet p(char_type());
    p.subtype().set(ID_C_constant, true);
    
    code_typet function_type;
    function_type.return_type()=empty_typet();
    function_type.arguments().push_back(
      code_typet::argumentt(p));

    symbolt new_symbol;
    new_symbol.name=full_id;
    new_symbol.base_name=id;
    new_symbol.type=function_type;
    
    symbol_table.move(new_symbol);

    s_it=symbol_table.symbols.find(full_id);
    assert(s_it!=symbol_table.symbols.end());
  }

  // signature is expected to be
  // (type *) -> ...
  if(s_it->second.type.id()!=ID_code ||
     to_code_type(s_it->second.type).arguments().size()!=1 ||
     to_code_type(s_it->second.type).arguments()[0].type().id()!=ID_pointer)
  {
    std::string error="function `"+id2string(id)+"' has wrong signature";
    throw error;
  }
  
  string_constantt function_id_string(argument);

  code_function_callt call;
  call.lhs().make_nil();
  call.function()=
    symbol_exprt(s_it->second.name, s_it->second.type);
  call.arguments().resize(1);
  call.arguments()[0]=
    typecast_exprt(
      address_of_exprt(index_exprt(
        function_id_string, gen_zero(index_type()))),
      to_code_type(s_it->second.type).arguments()[0].type());

  return call;
}

/*******************************************************************\

Function: function_enter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_enter(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    // don't instrument our internal functions
    if(has_prefix(id2string(f_it->first), CPROVER_PREFIX))
      continue;
    
    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(f_it->first=="c::"+id2string(id))
      continue;
    
    // patch in a call to `id' at the entry point
    goto_programt &body=f_it->second.body;
    
    goto_programt::targett t=
      body.insert_before(body.instructions.begin());
    t->make_function_call(
      function_to_call(symbol_table, id, f_it->first));
    t->function=f_it->first;
  }
}

/*******************************************************************\

Function: function_exit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_exit(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &id)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    // don't instrument our internal functions
    if(has_prefix(id2string(f_it->first), CPROVER_PREFIX))
      continue;
    
    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(f_it->first=="c::"+id2string(id))
      continue;
    
    // patch in a call to `id' at the exit points
    goto_programt &body=f_it->second.body;
    
    // make sure we have END_OF_FUNCTION
    if(body.instructions.empty() ||
       !body.instructions.back().is_end_function())
      body.add_instruction(END_FUNCTION);

    Forall_goto_program_instructions(i_it, body)
    {
      if(i_it->is_return())
      {
        goto_programt::instructiont call;
        call.function=f_it->first;
        call.make_function_call(
          function_to_call(symbol_table, id, f_it->first));
        body.insert_before_swap(i_it, call);

        // move on
        i_it++;
      }    
    }
      
    // exiting without return
    goto_programt::targett last=body.instructions.end();
    last--;
    assert(last->is_end_function());

    // is there already a return?
    bool has_return=false;
    
    if(last!=body.instructions.begin())
    {
      goto_programt::targett before_last=last;
      --before_last;
      if(before_last->is_return())
        has_return=true;
    }
    
    if(!has_return)
    {
      goto_programt::instructiont call;
      call.make_function_call(
        function_to_call(symbol_table, id, f_it->first));
      call.function=f_it->first;
      body.insert_before_swap(last, call);
    }
  }
}

