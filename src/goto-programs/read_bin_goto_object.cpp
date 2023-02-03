/*******************************************************************\

Module: Read goto object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Read goto object files.

#include "read_bin_goto_object.h"

#include <util/irep_serialization.h>
#include <util/message.h>
#include <util/symbol_table_base.h>

#include "goto_functions.h"
#include "write_goto_binary.h"

/// read goto binary format
/// \par parameters: input stream, symbol_table, functions
/// \return true on error, false otherwise
static bool read_bin_goto_object(
  std::istream &in,
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  irep_serializationt &irepconverter)
{
  std::size_t count = irepconverter.read_gb_word(in); // # of symbols

  for(std::size_t i=0; i<count; i++)
  {
    symbolt sym;

    sym.type = static_cast<const typet &>(irepconverter.reference_convert(in));
    sym.value = static_cast<const exprt &>(irepconverter.reference_convert(in));
    sym.location = static_cast<const source_locationt &>(
      irepconverter.reference_convert(in));

    sym.name = irepconverter.read_string_ref(in);
    sym.module = irepconverter.read_string_ref(in);
    sym.base_name = irepconverter.read_string_ref(in);
    sym.mode = irepconverter.read_string_ref(in);
    sym.pretty_name = irepconverter.read_string_ref(in);

    // obsolete: symordering
    irepconverter.read_gb_word(in);

    std::size_t flags=irepconverter.read_gb_word(in);

    sym.is_weak = (flags &(1 << 16))!=0;
    sym.is_type = (flags &(1 << 15))!=0;
    sym.is_property = (flags &(1 << 14))!=0;
    sym.is_macro = (flags &(1 << 13))!=0;
    sym.is_exported = (flags &(1 << 12))!=0;
    sym.is_input = (flags &(1 << 11))!=0;
    sym.is_output = (flags &(1 << 10))!=0;
    sym.is_state_var = (flags &(1 << 9))!=0;
    sym.is_parameter = (flags &(1 << 8))!=0;
    sym.is_auxiliary = (flags &(1 << 7))!=0;
    // sym.binding = (flags &(1 << 6))!=0;
    sym.is_lvalue = (flags &(1 << 5))!=0;
    sym.is_static_lifetime = (flags &(1 << 4))!=0;
    sym.is_thread_local = (flags &(1 << 3))!=0;
    sym.is_file_local = (flags &(1 << 2))!=0;
    sym.is_extern = (flags &(1 << 1))!=0;
    sym.is_volatile = (flags &1)!=0;

    if(!sym.is_type && sym.type.id()==ID_code)
    {
      // makes sure there is an empty function for every function symbol
      auto entry = functions.function_map.emplace(sym.name, goto_functiont());
      entry.first->second.set_parameter_identifiers(to_code_type(sym.type));
    }

    symbol_table.add(sym);
  }

  count=irepconverter.read_gb_word(in); // # of functions

  for(std::size_t fct_index = 0; fct_index < count; ++fct_index)
  {
    irep_idt fname=irepconverter.read_gb_string(in);
    goto_functionst::goto_functiont &f = functions.function_map[fname];

    typedef std::map<goto_programt::targett, std::list<unsigned> > target_mapt;
    target_mapt target_map;
    typedef std::map<unsigned, goto_programt::targett> rev_target_mapt;
    rev_target_mapt rev_target_map;

    bool hidden=false;

    std::size_t ins_count = irepconverter.read_gb_word(in); // # of instructions
    for(std::size_t ins_index = 0; ins_index < ins_count; ++ins_index)
    {
      goto_programt::targett itarget = f.body.add_instruction();

      // take copies as references into irepconverter are not stable
      codet code =
        static_cast<const codet &>(irepconverter.reference_convert(in));
      source_locationt source_location = static_cast<const source_locationt &>(
        irepconverter.reference_convert(in));
      goto_program_instruction_typet instruction_type =
        (goto_program_instruction_typet)irepconverter.read_gb_word(in);
      exprt guard =
        static_cast<const exprt &>(irepconverter.reference_convert(in));

      goto_programt::instructiont instruction{
        code, source_location, instruction_type, guard, {}};

      instruction.target_number = irepconverter.read_gb_word(in);
      if(instruction.is_target() &&
         rev_target_map.insert(
           rev_target_map.end(),
           std::make_pair(instruction.target_number, itarget))->second!=itarget)
        UNREACHABLE;

      std::size_t t_count = irepconverter.read_gb_word(in); // # of targets
      for(std::size_t i=0; i<t_count; i++)
        // just save the target numbers
        target_map[itarget].push_back(irepconverter.read_gb_word(in));

      std::size_t l_count = irepconverter.read_gb_word(in); // # of labels

      for(std::size_t i=0; i<l_count; i++)
      {
        irep_idt label=irepconverter.read_string_ref(in);
        instruction.labels.push_back(label);
        if(label == CPROVER_PREFIX "HIDE")
          hidden=true;
        // The above info is also held in the goto_functiont object, and could
        // be stored in the binary.
      }

      itarget->swap(instruction);
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
        INVARIANT(
          entry != rev_target_map.end(),
          "something from the target map should also be in the reverse target "
          "map");
        ins->targets.push_back(entry->second);
      }
    }

    f.body.update();

    if(hidden)
      f.make_hidden();
  }

  functions.compute_location_numbers();

  return false;
}

/// reads a goto binary file back into a symbol and a function table
/// \par parameters: input stream, symbol table, functions
/// \return true on error, false otherwise
bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  {
    char hdr[4];
    hdr[0]=static_cast<char>(in.get());
    hdr[1]=static_cast<char>(in.get());
    hdr[2]=static_cast<char>(in.get());

    if(hdr[0]=='G' && hdr[1]=='B' && hdr[2]=='F')
    {
      // OK!
    }
    else
    {
      hdr[3]=static_cast<char>(in.get());
      if(hdr[0]==0x7f && hdr[1]=='G' && hdr[2]=='B' && hdr[3]=='F')
      {
        // OK!
      }
      else if(hdr[0]==0x7f && hdr[1]=='E' && hdr[2]=='L' && hdr[3]=='F')
      {
        if(!filename.empty())
          message.error() << "Sorry, but I can't read ELF binary '" << filename
                          << "'" << messaget::eom;
        else
          message.error() << "Sorry, but I can't read ELF binaries"
                          << messaget::eom;

        return true;
      }
      else
      {
        message.error() << "'" << filename << "' is not a goto-binary"
                        << messaget::eom;
        return true;
      }
    }
  }

  irep_serializationt::ireps_containert ic;
  irep_serializationt irepconverter(ic);
  // symbol_serializationt symbolconverter(ic);

  {
    std::size_t version=irepconverter.read_gb_word(in);

    if(version < GOTO_BINARY_VERSION)
    {
      message.error() <<
          "The input was compiled with an old version of "
          "goto-cc; please recompile" << messaget::eom;
      return true;
    }
    else if(version == GOTO_BINARY_VERSION)
    {
      return read_bin_goto_object(in, symbol_table, functions, irepconverter);
    }
    else
    {
      message.error() <<
          "The input was compiled with an unsupported version of "
          "goto-cc; please recompile" << messaget::eom;
      return true;
    }
  }

  return false;
}
