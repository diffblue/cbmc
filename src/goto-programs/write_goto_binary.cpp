/*******************************************************************\

Module: Write GOTO binaries

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Write GOTO binaries

#include "write_goto_binary.h"

#include <fstream>

#include <util/irep_serialization.h>
#include <util/message.h>

#include <goto-programs/goto_model.h>

/// Writes the symbol table to file.
static void write_symbol_table_binary(
  std::ostream &out,
  const symbol_table_baset &symbol_table,
  irep_serializationt &irepconverter)
{
  write_gb_word(out, symbol_table.symbols.size());

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    // Since version 2, symbols are not converted to ireps,
    // instead they are saved in a custom binary format

    const symbolt &sym = symbol_pair.second;

    irepconverter.reference_convert(sym.type, out);
    irepconverter.reference_convert(sym.value, out);
    irepconverter.reference_convert(sym.location, out);

    irepconverter.write_string_ref(out, sym.name);
    irepconverter.write_string_ref(out, sym.module);
    irepconverter.write_string_ref(out, sym.base_name);
    irepconverter.write_string_ref(out, sym.mode);
    irepconverter.write_string_ref(out, sym.pretty_name);

    write_gb_word(out, 0); // old: sym.ordering

    unsigned flags=0;
    flags = (flags << 1) | static_cast<int>(sym.is_weak);
    flags = (flags << 1) | static_cast<int>(sym.is_type);
    flags = (flags << 1) | static_cast<int>(sym.is_property);
    flags = (flags << 1) | static_cast<int>(sym.is_macro);
    flags = (flags << 1) | static_cast<int>(sym.is_exported);
    flags = (flags << 1) | static_cast<int>(sym.is_input);
    flags = (flags << 1) | static_cast<int>(sym.is_output);
    flags = (flags << 1) | static_cast<int>(sym.is_state_var);
    flags = (flags << 1) | static_cast<int>(sym.is_parameter);
    flags = (flags << 1) | static_cast<int>(sym.is_auxiliary);
    flags = (flags << 1) | static_cast<int>(false); // sym.binding;
    flags = (flags << 1) | static_cast<int>(sym.is_lvalue);
    flags = (flags << 1) | static_cast<int>(sym.is_static_lifetime);
    flags = (flags << 1) | static_cast<int>(sym.is_thread_local);
    flags = (flags << 1) | static_cast<int>(sym.is_file_local);
    flags = (flags << 1) | static_cast<int>(sym.is_extern);
    flags = (flags << 1) | static_cast<int>(sym.is_volatile);

    write_gb_word(out, flags);
  }
}

static void write_instructions_binary(
  std::ostream &out,
  irep_serializationt &irepconverter,
  const std::pair<const irep_idt, goto_functiont> &fct)
{
  write_gb_word(out, fct.second.body.instructions.size());

  for(const auto &instruction : fct.second.body.instructions)
  {
    irepconverter.reference_convert(instruction.code(), out);
    irepconverter.reference_convert(instruction.source_location(), out);
    write_gb_word(out, (long)instruction.type());

    const auto condition =
      instruction.has_condition() ? instruction.condition() : true_exprt();
    irepconverter.reference_convert(condition, out);

    write_gb_word(out, instruction.target_number);

    write_gb_word(out, instruction.targets.size());

    for(const auto &t_it : instruction.targets)
      write_gb_word(out, t_it->target_number);

    write_gb_word(out, instruction.labels.size());

    for(const auto &l_it : instruction.labels)
      irepconverter.write_string_ref(out, l_it);
  }
}

/// Writes the functions to file, but only those with non-empty body.
static void write_goto_functions_binary(
  std::ostream &out,
  const goto_functionst &goto_functions,
  irep_serializationt &irepconverter)
{
  unsigned cnt=0;
  for(const auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
      cnt++;
  }

  write_gb_word(out, cnt);

  for(const auto &fct : goto_functions.function_map)
  {
    if(!fct.second.body_available())
      continue;

    // Since version 2, goto functions are not converted to ireps,
    // instead they are saved in a custom binary format

    const auto function_name = id2string(fct.first);
    write_gb_string(out, function_name);
    write_instructions_binary(out, irepconverter, fct);
  }
}

/// Writes a goto program to disc, using goto binary format
static void write_goto_binary(
  std::ostream &out,
  const symbol_table_baset &symbol_table,
  const goto_functionst &goto_functions,
  irep_serializationt &irepconverter)
{
  write_symbol_table_binary(out, symbol_table, irepconverter);
  write_goto_functions_binary(out, goto_functions, irepconverter);
}

/// Writes a goto program to disc
bool write_goto_binary(
  std::ostream &out,
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  int version)
{
  return write_goto_binary(
    out,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler,
    version);
}

/// Writes a goto program to disc
bool write_goto_binary(
  std::ostream &out,
  const symbol_table_baset &symbol_table,
  const goto_functionst &goto_functions,
  message_handlert &message_handler,
  int version)
{
  // header
  out << char(0x7f) << "GBF";
  write_gb_word(out, version);

  irep_serializationt::ireps_containert irepc;
  irep_serializationt irepconverter(irepc);

  if(version < GOTO_BINARY_VERSION)
  {
    messaget message{message_handler};
    message.error() << "version " << version << " no longer supported; "
                    << "supported version = " << GOTO_BINARY_VERSION
                    << messaget::eom;
    return true;
  }
  if(version > GOTO_BINARY_VERSION)
  {
    messaget message{message_handler};
    message.error() << "unknown goto binary version " << version << "; "
                    << "supported version = " << GOTO_BINARY_VERSION
                    << messaget::eom;
    return true;
  }
  write_goto_binary(out, symbol_table, goto_functions, irepconverter);
  return false;
}

/// Writes a goto program to disc
bool write_goto_binary(
  const std::string &filename,
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::ofstream out(filename, std::ios::binary);

  if(!out)
  {
    messaget message(message_handler);
    message.error() << "Failed to open '" << filename << "'";
    return true;
  }

  return write_goto_binary(out, goto_model, message_handler);
}
