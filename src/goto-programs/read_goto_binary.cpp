/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <fstream>

#include <util/message.h>
#include <util/unicode.h>
#include <util/tempfile.h>
#include <util/rename_symbol.h>
#include <util/base_type.h>

#include <langapi/language_ui.h>

#include <linking/linking_class.h>

#include "goto_model.h"
#include "read_goto_binary.h"
#include "read_bin_goto_object.h"
#include "elf_reader.h"
#include "osx_fat_reader.h"

/*******************************************************************\

Function: read_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool read_goto_binary(
  const std::string &filename,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  return read_goto_binary(
    filename, dest.symbol_table, dest.goto_functions, message_handler);
}

/*******************************************************************\

Function: read_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename).c_str(), std::ios::binary);
  #else
  std::ifstream in(filename.c_str(), std::ios::binary);
  #endif

  if(!in)
  {
    messaget message(message_handler);
    message.error() << "Failed to open `" << filename << "'"
                    << messaget::eom;
    return true;
  }
  
  char hdr[4];
  hdr[0]=in.get();
  hdr[1]=in.get();
  hdr[2]=in.get();    
  hdr[3]=in.get();
  in.seekg(0);

  if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
  {
    return read_bin_goto_object(
      in, filename, symbol_table, goto_functions, message_handler);
  }
  else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
  {
    // ELF binary.
    // This _may_ have a goto-cc section.
    try
    {
      elf_readert elf_reader(in);
      
      for(unsigned i=0; i<elf_reader.number_of_sections; i++)
        if(elf_reader.section_name(i)=="goto-cc")
        {
          in.seekg(elf_reader.section_offset(i));
          return read_bin_goto_object(
            in, filename, symbol_table, goto_functions, message_handler);
        }
        
      // section not found
      messaget(message_handler).error() <<
        "failed to find goto-cc section in ELF binary" << messaget::eom;
    }
    
    catch(const char *s)
    {
      messaget(message_handler).error() << s << messaget::eom;
    }
  }
  else if(is_osx_fat_magic(hdr))
  {
    std::string tempname;
    // Mach-O universal binary
    // This _may_ have a goto binary as hppa7100LC architecture
    try
    {
      osx_fat_readert osx_fat_reader(in);

      if(osx_fat_reader.has_gb())
      {
        tempname=get_temporary_file("tmp.goto-binary", ".gb");
        osx_fat_reader.extract_gb(filename, tempname);

        std::ifstream temp_in(tempname.c_str(), std::ios::binary);
        if(!temp_in)
          messaget(message_handler).error() << "failed to read temp binary" << messaget::eom;
        const bool read_err=read_bin_goto_object(
          temp_in, filename, symbol_table, goto_functions, message_handler);
        temp_in.close();

        unlink(tempname.c_str());
        return read_err;
      }

      // architecture not found
      messaget(message_handler).error() <<
        "failed to find goto binary in Mach-O file" << messaget::eom;
    }

    catch(const char *s)
    {
      if(!tempname.empty())
        unlink(tempname.c_str());
      messaget(message_handler).error() << s << messaget::eom;
    }
  }
  else
  {
    messaget(message_handler).error() <<
      "not a goto binary" << messaget::eom;
  }
  
  return true;
}

/*******************************************************************\

Function: is_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_goto_binary(const std::string &filename)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename).c_str(), std::ios::binary);
  #else
  std::ifstream in(filename.c_str(), std::ios::binary);
  #endif
  
  if(!in) return false;
  
  // We accept two forms:
  // 1. goto binaries, marked with 0x7f GBF
  // 2. ELF binaries, marked with 0x7f ELF

  char hdr[4];
  hdr[0]=in.get();
  hdr[1]=in.get();
  hdr[2]=in.get();    
  hdr[3]=in.get();

  if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
  {
    return true; // yes, this is a goto binary
  }
  else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
  {
    // this _may_ have a goto-cc section
    try
    {
      in.seekg(0);
      elf_readert elf_reader(in);
      if(elf_reader.has_section("goto-cc")) return true;
    }
    
    catch(...)
    {
      // ignore any errors
    }
  }
  else if(is_osx_fat_magic(hdr))
  {
    // this _may_ have a goto binary as hppa7100LC architecture
    try
    {
      in.seekg(0);
      osx_fat_readert osx_fat_reader(in);
      if(osx_fat_reader.has_gb()) return true;
    }
    
    catch(...)
    {
      // ignore any errors
    }
  }
  
  return false;
}

/*******************************************************************\

Function: rename_symbols_in_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void rename_symbols_in_function(
  goto_functionst::goto_functiont &function,
  const rename_symbolt &rename_symbol)
{
  goto_programt &program=function.body;
  rename_symbol(function.type);

  Forall_goto_program_instructions(iit, program)
  {
    rename_symbol(iit->code);
    rename_symbol(iit->guard);
  }
}

/*******************************************************************\

Function: link_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool link_functions(
  symbol_tablet &dest_symbol_table,
  goto_functionst &dest_functions,
  symbol_tablet &src_symbol_table,
  goto_functionst &src_functions,
  const rename_symbolt &rename_symbol)
{
  namespacet ns(dest_symbol_table);

  // merge functions
  Forall_goto_functions(src_it, src_functions)
  {
    // the function might have been renamed
    rename_symbolt::expr_mapt::const_iterator e_it=
      rename_symbol.expr_map.find(src_it->first);

    irep_idt final_id=src_it->first;

    if(e_it!=rename_symbol.expr_map.end())
      final_id=e_it->second;

    // already there?
    goto_functionst::function_mapt::iterator dest_f_it=
      dest_functions.function_map.find(final_id);

    if(dest_f_it==dest_functions.function_map.end()) // not there yet
    {
      rename_symbols_in_function(src_it->second, rename_symbol);

      goto_functionst::goto_functiont &in_dest_symbol_table=
        dest_functions.function_map[final_id];

      in_dest_symbol_table.body.swap(src_it->second.body);
      in_dest_symbol_table.body_available=src_it->second.body_available;
      in_dest_symbol_table.type=src_it->second.type;
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_dest_symbol_table=
        dest_functions.function_map[final_id];

      goto_functionst::goto_functiont &src_func=src_it->second;

      if(in_dest_symbol_table.body.instructions.empty())
      {
        // the one with body wins!
        rename_symbols_in_function(src_func, rename_symbol);

        in_dest_symbol_table.body.swap(src_func.body);
        in_dest_symbol_table.body_available=src_func.body_available;
        in_dest_symbol_table.type=src_func.type;
      }
      else if(src_func.body.instructions.empty())
      {
        // just keep the old one in dest
      }
      else if(in_dest_symbol_table.type.get_bool(ID_C_inlined))
      {
        // ok, we silently ignore
      }
      else
      {
        // the linking code will have ensured that types match
        rename_symbol(src_func.type);
        assert(base_type_eq(in_dest_symbol_table.type, src_func.type, ns));
      }
    }
  }

  return false;
}

/*******************************************************************\

Function: read_object_and_link

  Inputs: a file_name

 Outputs: true on error, false otherwise

 Purpose: reads an object file

\*******************************************************************/

bool read_object_and_link(
  const std::string &file_name,
  symbol_tablet &symbol_table,
  goto_functionst &functions,
  language_uit &language_ui)
{
  language_ui.print(8, "Reading: " + file_name);

  // we read into a temporary symbol_table
  symbol_tablet temp_symbol_table;
  goto_functionst temp_functions;

  if(read_goto_binary(
      file_name,
      temp_symbol_table,
      temp_functions,
      language_ui.get_message_handler()))
    return true;

  std::set<irep_idt> seen_modes;

  for(symbol_tablet::symbolst::const_iterator
      it=temp_symbol_table.symbols.begin();
      it!=temp_symbol_table.symbols.end();
      it++)
  {
    if(it->second.mode!="")
      seen_modes.insert(it->second.mode);
  }

  seen_modes.erase(ID_cpp);
  seen_modes.erase(ID_C);

  if(!seen_modes.empty())
  {
    language_ui.error() << "Multi-language linking not supported"
                        << messaget::eom;
    return true;
  }

  // hardwired to C-style linking

  linkingt linking(symbol_table,
                   temp_symbol_table,
                   language_ui.get_message_handler());

  if(linking.typecheck_main())
    return true;

  if(link_functions(symbol_table, functions,
                    temp_symbol_table, temp_functions,
                    linking.rename_symbol))
    return true;

  return false;
}

