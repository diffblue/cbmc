/*******************************************************************\
 
Module: Read goto object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#include <namespace.h>
#include <message_stream.h>
#include <context.h>

#include "read_bin_goto_object.h"
#include "goto_function_serialization.h"
#include "irep_serialization.h"
#include "goto_program_irep.h"

/*******************************************************************\
 
Function: read_goto_object_v2
 
  Inputs: input stream, context, functions
 
 Outputs: true on error, false otherwise
 
 Purpose: read goto binary format v2
 
\*******************************************************************/

bool read_bin_goto_object_v2(
  std::istream &in,
  const std::string &filename,
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler,
  irep_serializationt &irepconverter,
  goto_function_serializationt &gfconverter)
{ 
  unsigned count = irepconverter.read_long(in); // # of symbols

  for(unsigned i=0; i<count; i++)
  {
    symbolt sym;
      
    irepconverter.reference_convert(in, sym.type);
    irepconverter.reference_convert(in, sym.value);
    irepconverter.reference_convert(in, sym.location);
    
    sym.name = irepconverter.read_string_ref(in);
    sym.module = irepconverter.read_string_ref(in);
    sym.base_name = irepconverter.read_string_ref(in);
    sym.mode = irepconverter.read_string_ref(in);
    sym.pretty_name = irepconverter.read_string_ref(in);
    
    // obsolete: symordering
    irepconverter.read_long(in);

    unsigned flags=irepconverter.read_long(in);
    
    sym.is_type = flags & (1 << 15);
    sym.is_property = flags & (1 << 14); 
    sym.is_macro = flags & (1 << 13);
    sym.is_exported = flags & (1 << 12);
    sym.is_input = flags & (1 << 11);
    sym.is_output = flags & (1 << 10);
    sym.is_state_var = flags & (1 << 9);
    sym.is_argument = flags & (1 << 8);
    //sym.free_var = flags & (1 << 7);
    //sym.binding = flags & (1 << 6);
    sym.is_lvalue = flags & (1 << 5);
    sym.is_static_lifetime = flags & (1 << 4);
    sym.is_thread_local = flags & (1 << 3);
    sym.is_file_local = flags & (1 << 2);
    sym.is_extern = flags & (1 << 1);
    sym.is_volatile = flags & 1;
    
    if(!sym.is_type && sym.type.id()==ID_code)
    {
      // makes sure there is an empty function
      // for every function symbol and fixes
      // the function types. 
      functions.function_map[sym.name].type=to_code_type(sym.type);      
    }
    
    context.add(sym);
  }
  
  count=irepconverter.read_long(in); // # of functions
  
  for(unsigned i=0; i<count; i++)
  {    
    irep_idt fname=irepconverter.read_string(in);
    goto_functionst::goto_functiont &f = functions.function_map[fname];
    
    typedef std::map<goto_programt::targett, std::list<unsigned> > target_mapt;
    target_mapt target_map;
    typedef std::map<unsigned, goto_programt::targett> rev_target_mapt;
    rev_target_mapt rev_target_map;
    
    unsigned ins_count = irepconverter.read_long(in); // # of instructions
    for (unsigned i=0; i<ins_count; i++)
    {
      goto_programt::targett itarget = f.body.add_instruction();
      goto_programt::instructiont &instruction=*itarget;
      
      irepconverter.reference_convert(in, instruction.code);
      instruction.function = irepconverter.read_string_ref(in);      
      irepconverter.reference_convert(in, instruction.location);
      instruction.type = (goto_program_instruction_typet) 
                              irepconverter.read_long(in);
      instruction.guard.make_nil();
      irepconverter.reference_convert(in, instruction.guard);
      irepconverter.read_string_ref(in); // former event
      instruction.target_number = irepconverter.read_long(in);
      if(instruction.is_target() &&
          rev_target_map.insert(rev_target_map.end(),
            std::make_pair(instruction.target_number, itarget))->second!=itarget)
        assert(false);
      
      unsigned t_count = irepconverter.read_long(in); // # of targets
      for (unsigned i=0; i<t_count; i++)
        // just save the target numbers
        target_map[itarget].push_back(irepconverter.read_long(in));
        
      unsigned l_count = irepconverter.read_long(in); // # of labels
      for (unsigned i=0; i<l_count; i++)
        instruction.labels.push_back(irepconverter.read_string_ref(in));
    }
    
    // Resolve targets
    for(target_mapt::iterator tit = target_map.begin();
        tit!=target_map.end();
        tit++)
    {
      goto_programt::targett ins = tit->first;
      
      for(std::list<unsigned>::iterator nit = tit->second.begin();
          nit!=tit->second.end();
          nit++)
      {
        unsigned n=*nit;
        rev_target_mapt::const_iterator entry=rev_target_map.find(n);
        assert(entry!=rev_target_map.end());
        ins->targets.push_back(entry->second);
      }
    }
    
    f.body.update();
    f.body_available=f.body.instructions.size()>0;    
  }
  
  return false;
}

/*******************************************************************\
 
Function: read_goto_object
 
  Inputs: input stream, context, functions
 
 Outputs: true on error, false otherwise
 
 Purpose: reads a goto binary file back into a symbol and a function table
 
\*******************************************************************/

bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler)
{ 
  message_streamt message_stream(message_handler);

  {
    char hdr[4];
    hdr[0]=in.get();
    hdr[1]=in.get();
    hdr[2]=in.get();    

    if(hdr[0]=='G' && hdr[1]=='B' && hdr[2]=='F')
	   ;
    else
    {
      hdr[3]=in.get();
      if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
      {
        // OK!
      }
      else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
      {
        if(filename!="")
          message_stream.str << 
            "Sorry, but I can't read ELF binary `" << filename << "'";
        else
          message_stream.str << "Sorry, but I can't read ELF binaries";
  
        message_stream.error();
        return true;
      }
      else
      {
        message_stream.str << "`" << filename << "' is not a goto-binary";
        message_stream.error();
        return true;
      } 
    }
  }
  
  irep_serializationt::ireps_containert ic;
  irep_serializationt irepconverter(ic);
  //symbol_serializationt symbolconverter(ic);
  goto_function_serializationt gfconverter(ic);
  
  {
    unsigned version=irepconverter.read_long(in);
        
    switch(version)
    {
    case 1:
      message_stream.warning(
          "The input was compiled with an old version of "
          "goto-cc; please recompile");
      return true;

    case 2:
      return read_bin_goto_object_v2(in, filename, 
                                     context, functions, 
                                     message_handler,
                                     irepconverter,
                                     gfconverter); 
      break;

    default:
      message_stream.warning(
          "The input was compiled with an unsupported version of "
          "goto-cc; please recompile");
      return true;
    }
  } 
   
  return false;
}
