/*******************************************************************\

Module: Write GOTO binaries

Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>

#include <message.h>
#include <irep_serialization.h>
#include <symbol_serialization.h>
#include <context.h>

#include <goto-programs/goto_function_serialization.h>

#include "write_goto_binary.h"

/*******************************************************************\

Function: goto_programt::write_goto_binary_v2

  Inputs:

 Outputs:

 Purpose: Writes a goto program to disc, using goto binary format ver 2

\*******************************************************************/

bool write_goto_binary_v2(
  std::ostream &out,
  const contextt &lcontext,
  const goto_functionst &functions,
  irep_serializationt &irepconverter,  
  goto_function_serializationt &gfconverter)
{
  // first write symbol table

  write_long(out, lcontext.symbols.size());

  forall_symbols(it, lcontext.symbols)
  {
    // In version 2, symbols are not converted to ireps,
    // instead they are saved in a custom binary format
    
    const symbolt &sym = it->second;        
    
    irepconverter.reference_convert(sym.type, out);
    irepconverter.reference_convert(sym.value, out);
    irepconverter.reference_convert(sym.location, out);
    
    irepconverter.write_string_ref(out, sym.name);
    irepconverter.write_string_ref(out, sym.module);
    irepconverter.write_string_ref(out, sym.base_name);
    irepconverter.write_string_ref(out, sym.mode);
    irepconverter.write_string_ref(out, sym.pretty_name);
    
    write_long(out, sym.ordering);

    unsigned flags=0;    
    flags = (flags << 1) | (int)sym.is_type; 
    flags = (flags << 1) | (int)sym.theorem;
    flags = (flags << 1) | (int)sym.is_macro;
    flags = (flags << 1) | (int)sym.is_exported;
    flags = (flags << 1) | (int)sym.is_input;
    flags = (flags << 1) | (int)sym.is_output;
    flags = (flags << 1) | (int)sym.is_statevar;
    flags = (flags << 1) | (int)sym.is_actual;
    flags = (flags << 1) | (int)sym.free_var;
    flags = (flags << 1) | (int)sym.binding;
    flags = (flags << 1) | (int)sym.lvalue;
    flags = (flags << 1) | (int)sym.static_lifetime;
    flags = (flags << 1) | (int)sym.thread_local;
    flags = (flags << 1) | (int)sym.file_local;
    flags = (flags << 1) | (int)sym.is_extern;
    flags = (flags << 1) | (int)sym.is_volatile;
    
    write_long(out, flags);
  }

  // now write functions, but only those with body

  unsigned cnt=0;
  forall_goto_functions(it, functions)  
    if(it->second.body_available)
      cnt++;

  write_long(out, cnt);

  for(goto_functionst::function_mapt::const_iterator
      it=functions.function_map.begin();
      it!=functions.function_map.end();
      it++)
  {
    if(it->second.body_available)
    {      
      // In version 2, goto functions are not converted to ireps,
      // instead they are saved in a custom binary format      
      
      write_string(out, it->first.as_string()); // name      
      write_long(out, it->second.body.instructions.size()); // # instructions
      
      forall_goto_program_instructions(i_it, it->second.body)
      {
        const goto_programt::instructiont &instruction = *i_it;
        
        irepconverter.reference_convert(instruction.code, out);
        irepconverter.write_string_ref(out, instruction.function);
        irepconverter.reference_convert(instruction.location, out);
        write_long(out, (long)instruction.type);
        irepconverter.reference_convert(instruction.guard, out);        
        irepconverter.write_string_ref(out, irep_idt()); // former event
        write_long(out, instruction.target_number);
                
        write_long(out, instruction.targets.size());

        for(goto_programt::targetst::const_iterator
            t_it=instruction.targets.begin();
            t_it!=instruction.targets.end();
            t_it++)
          write_long(out, (*t_it)->target_number);
          
        write_long(out, instruction.labels.size());

        for(goto_programt::instructiont::labelst::const_iterator
            l_it=instruction.labels.begin();
            l_it!=instruction.labels.end();
            l_it++)
          irepconverter.write_string_ref(out, *l_it);
      }
    }
  }

  //irepconverter.output_map(f);
  //irepconverter.output_string_map(f);  

  return false;
}

/*******************************************************************\

Function: goto_programt::write_goto_binary

  Inputs:

 Outputs:

 Purpose: Writes a goto program to disc

\*******************************************************************/

bool write_goto_binary(
  std::ostream &out,
  const contextt &lcontext,
  const goto_functionst &functions,
  int version)
{
  // header
  out << char(0x7f) << "GBF";
  write_long(out, version);

  irep_serializationt::ireps_containert irepc;
  irep_serializationt irepconverter(irepc);    
  goto_function_serializationt gfconverter(irepc);
    
  switch(version)
  {
  case 1: 
    throw "version 1 no longer supported";

  case 2:
    return write_goto_binary_v2(
      out, lcontext, functions,
      irepconverter,
      gfconverter); 

  default: 
    throw "Unknown goto binary version";
  }
  
  return false;
}

/*******************************************************************\

Function: goto_programt::write_goto_binary

  Inputs:

 Outputs:

 Purpose: Writes a goto program to disc

\*******************************************************************/

bool write_goto_binary(
  const std::string &filename,
  const contextt &context,
  const goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  std::ofstream out(filename.c_str(), std::ios::binary);

  if(!out)
  {
    messaget message(message_handler);
    message.error(
      std::string("Failed to open `")+filename+"'");
    return true;
  }

  return write_goto_binary(out, context, goto_functions);
}

