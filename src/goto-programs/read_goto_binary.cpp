/*******************************************************************\

Module: Read Goto Programs

Author:

\*******************************************************************/

/// \file
/// Read Goto Programs

#include "read_goto_binary.h"

#include <fstream>

#include <util/base_type.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/message.h>
#include <util/tempfile.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <linking/linking_class.h>

#include "goto_model.h"
#include "read_bin_goto_object.h"
#include "elf_reader.h"
#include "osx_fat_reader.h"

static void rename_symbols_in_function(
  goto_functionst::goto_functiont &function,
  irep_idt &new_function_name,
  const rename_symbolt &rename_symbol)
{
  for(auto &identifier : function.parameter_identifiers)
  {
    auto entry = rename_symbol.expr_map.find(identifier);
    if(entry != rename_symbol.expr_map.end())
      identifier = entry->second;
  }

  for(auto &instruction : function.body.instructions)
  {
    rename_symbol(instruction.code_nonconst());

    if(instruction.has_condition())
    {
      exprt c = instruction.get_condition();
      rename_symbol(c);
      instruction.set_condition(c);
    }
  }
}

/// Link a set of goto functions, considering weak symbols
/// and symbol renaming
static bool link_functions(
  symbol_tablet &dest_symbol_table,
  goto_functionst &dest_functions,
  const symbol_tablet &src_symbol_table,
  goto_functionst &src_functions,
  const rename_symbolt &rename_symbol,
  const std::unordered_set<irep_idt> &weak_symbols)
{
  namespacet ns(dest_symbol_table);
  namespacet src_ns(src_symbol_table);

  // merge functions
  for(auto &gf_entry : src_functions.function_map)
  {
    // the function might have been renamed
    rename_symbolt::expr_mapt::const_iterator e_it =
      rename_symbol.expr_map.find(gf_entry.first);

    irep_idt final_id = gf_entry.first;

    if(e_it != rename_symbol.expr_map.end())
      final_id = e_it->second;

    // already there?
    goto_functionst::function_mapt::iterator dest_f_it =
      dest_functions.function_map.find(final_id);

    goto_functionst::goto_functiont &src_func = gf_entry.second;
    if(dest_f_it == dest_functions.function_map.end()) // not there yet
    {
      rename_symbols_in_function(src_func, final_id, rename_symbol);
      dest_functions.function_map.emplace(final_id, std::move(src_func));
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_dest_symbol_table = dest_f_it->second;

      if(
        in_dest_symbol_table.body.instructions.empty() ||
        weak_symbols.find(final_id) != weak_symbols.end())
      {
        // the one with body wins!
        rename_symbols_in_function(src_func, final_id, rename_symbol);

        in_dest_symbol_table.body.swap(src_func.body);
        in_dest_symbol_table.parameter_identifiers.swap(
          src_func.parameter_identifiers);
      }
      else if(
        src_func.body.instructions.empty() ||
        src_ns.lookup(gf_entry.first).is_weak)
      {
        // just keep the old one in dest
      }
      else if(to_code_type(ns.lookup(final_id).type).get_inlined())
      {
        // ok, we silently ignore
      }
      else
      {
        // the linking code will have ensured that types match
      }
    }
  }

  return false;
}

static void link_goto_model(
  goto_modelt &dest,
  goto_modelt &src,
  unchecked_replace_symbolt &object_type_updates,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> weak_symbols;

  for(const auto &symbol_pair : dest.symbol_table.symbols)
  {
    if(symbol_pair.second.is_weak)
      weak_symbols.insert(symbol_pair.first);
  }

  linkingt linking(dest.symbol_table, src.symbol_table, message_handler);

  if(linking.typecheck_main())
    throw invalid_source_file_exceptiont("typechecking main failed");

  if(link_functions(
       dest.symbol_table,
       dest.goto_functions,
       src.symbol_table,
       src.goto_functions,
       linking.rename_symbol,
       weak_symbols))
  {
    throw invalid_source_file_exceptiont("linking failed");
  }

  object_type_updates.get_expr_map().insert(
    linking.object_type_updates.get_expr_map().begin(),
    linking.object_type_updates.get_expr_map().end());
}

static void finalize_linking(
  goto_modelt &dest,
  const unchecked_replace_symbolt &object_type_updates)
{
  goto_functionst &dest_functions = dest.goto_functions;
  symbol_tablet &dest_symbol_table = dest.symbol_table;

  // apply macros
  rename_symbolt macro_application;

  for(const auto &symbol_pair : dest_symbol_table.symbols)
  {
    if(symbol_pair.second.is_macro && !symbol_pair.second.is_type)
    {
      const symbolt &symbol = symbol_pair.second;

      INVARIANT(symbol.value.id() == ID_symbol, "must have symbol");
      const irep_idt &id = to_symbol_expr(symbol.value).get_identifier();

#if 0
      if(!base_type_eq(symbol.type, ns.lookup(id).type, ns))
      {
        std::cerr << symbol << '\n';
        std::cerr << ns.lookup(id) << '\n';
      }
      INVARIANT(base_type_eq(symbol.type, ns.lookup(id).type, ns),
                "type matches");
#endif

      macro_application.insert_expr(symbol.name, id);
    }
  }

  if(!macro_application.expr_map.empty())
  {
    for(auto &gf_entry : dest_functions.function_map)
    {
      irep_idt final_id = gf_entry.first;
      rename_symbols_in_function(gf_entry.second, final_id, macro_application);
    }
  }

  if(!object_type_updates.empty())
  {
    for(auto &gf_entry : dest_functions.function_map)
    {
      Forall_goto_program_instructions(iit, gf_entry.second.body)
      {
        iit->transform([&object_type_updates](exprt expr) {
          object_type_updates(expr);
          return expr;
        });
      }
    }
  }
}

static bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &,
  goto_functionst &,
  message_handlert &);

/// \brief Read a goto binary from a file, but do not update \ref config
/// \param filename: the file name of the goto binary
/// \param message_handler: for diagnostics
/// \return goto model on success, {} on failure
optionalt<goto_modelt>
read_goto_binary(const std::string &filename, message_handlert &message_handler)
{
  goto_modelt dest;

  if(read_goto_binary(
       filename, dest.symbol_table, dest.goto_functions, message_handler))
  {
    return {};
  }
  else
    return std::move(dest);
}

/// \brief Read a goto binary from a file, but do not update \ref config
/// \param filename: the file name of the goto binary
/// \param symbol_table: the symbol table from the goto binary
/// \param goto_functions: the goto functions from the goto binary
/// \param message_handler: for diagnostics
/// \return true on failure, false on success
static bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename), std::ios::binary);
  #else
  std::ifstream in(filename, std::ios::binary);
  #endif

  messaget message(message_handler);

  if(!in)
  {
    message.error() << "Failed to open '" << filename << "'" << messaget::eom;
    return true;
  }

  char hdr[8];
  in.read(hdr, 8);
  if(!in)
  {
    message.error() << "Failed to read header from '" << filename << "'"
                    << messaget::eom;
    return true;
  }

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
  else if(is_osx_fat_header(hdr))
  {
    messaget message(message_handler);

    // Mach-O universal binary
    // This _may_ have a goto binary as hppa7100LC architecture
    osx_fat_readert osx_fat_reader(in, message_handler);

    if(osx_fat_reader.has_gb())
    {
      temporary_filet tempname("tmp.goto-binary", ".gb");
      if(osx_fat_reader.extract_gb(filename, tempname()))
      {
        message.error() << "failed to extract goto binary" << messaget::eom;
        return true;
      }

      std::ifstream temp_in(tempname(), std::ios::binary);
      if(!temp_in)
        message.error() << "failed to read temp binary" << messaget::eom;

      const bool read_err = read_bin_goto_object(
        temp_in, filename, symbol_table, goto_functions, message_handler);
      temp_in.close();

      return read_err;
    }

    // architecture not found
    message.error() << "failed to find goto binary in Mach-O file"
                    << messaget::eom;
  }
  else if(is_osx_mach_object(hdr))
  {
    messaget message(message_handler);

    // Mach-O object file, may contain a goto-cc section
    try
    {
      osx_mach_o_readert mach_o_reader(in, message_handler);

      osx_mach_o_readert::sectionst::const_iterator entry =
        mach_o_reader.sections.find("goto-cc");
      if(entry != mach_o_reader.sections.end())
      {
        in.seekg(entry->second.offset);
        return read_bin_goto_object(
          in, filename, symbol_table, goto_functions, message_handler);
      }

      // section not found
      messaget(message_handler).error()
        << "failed to find goto-cc section in Mach-O binary" << messaget::eom;
    }

    catch(const deserialization_exceptiont &e)
    {
      messaget(message_handler).error() << e.what() << messaget::eom;
    }
  }
  else
  {
    messaget(message_handler).error() <<
      "not a goto binary" << messaget::eom;
  }

  return true;
}

bool is_goto_binary(
  const std::string &filename,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream in(widen(filename), std::ios::binary);
  #else
  std::ifstream in(filename, std::ios::binary);
  #endif

  if(!in)
    return false;

  // We accept two forms:
  // 1. goto binaries, marked with 0x7f GBF
  // 2. ELF binaries, marked with 0x7f ELF

  char hdr[8];
  in.read(hdr, 8);
  if(!in)
    return false;

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
      if(elf_reader.has_section("goto-cc"))
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }
  else if(is_osx_fat_header(hdr))
  {
    // this _may_ have a goto binary as hppa7100LC architecture
    try
    {
      in.seekg(0);
      osx_fat_readert osx_fat_reader(in, message_handler);
      if(osx_fat_reader.has_gb())
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }
  else if(is_osx_mach_object(hdr))
  {
    // this _may_ have a goto-cc section
    try
    {
      in.seekg(0);
      osx_mach_o_readert mach_o_reader(in, message_handler);
      if(mach_o_reader.has_section("goto-cc"))
        return true;
    }

    catch(...)
    {
      // ignore any errors
    }
  }

  return false;
}

/// \brief reads an object file, and also updates config
/// \param file_name: file name of the goto binary
/// \param dest: the goto model returned
/// \param [out] object_type_updates: collects type replacements to be applied
/// \param message_handler: for diagnostics
/// \return true on error, false otherwise
static bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &dest,
  unchecked_replace_symbolt &object_type_updates,
  message_handlert &message_handler)
{
  messaget(message_handler).status()
    << "Reading GOTO program from file " << file_name << messaget::eom;

  // we read into a temporary model
  auto temp_model = read_goto_binary(file_name, message_handler);
  if(!temp_model.has_value())
    return true;

  try
  {
    link_goto_model(dest, *temp_model, object_type_updates, message_handler);
  }
  catch(...)
  {
    return true;
  }

  return false;
}

bool read_objects_and_link(
  const std::list<std::string> &file_names,
  goto_modelt &dest,
  message_handlert &message_handler)
{
  if(file_names.empty())
    return false;

  unchecked_replace_symbolt object_type_updates;

  for(const auto &file_name : file_names)
  {
    const bool failed = read_object_and_link(
      file_name, dest, object_type_updates, message_handler);

    if(failed)
      return true;
  }

  finalize_linking(dest, object_type_updates);

  // reading successful, let's update config
  config.set_from_symbol_table(dest.symbol_table);

  return false;
}
