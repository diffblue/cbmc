/// Author: Diffblue Ltd.

/// \file
/// Model for lazy loading of functions

#include "lazy_goto_model.h"
#include "read_goto_binary.h"
#include "rebuild_goto_start_function.h"

#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/journalling_symbol_table.h>
#include <util/unicode.h>

#include <langapi/language.h>

#include <fstream>

//! @cond Doxygen_suppress_Lambda_in_initializer_list
lazy_goto_modelt::lazy_goto_modelt(
  post_process_functiont post_process_function,
  post_process_functionst post_process_functions,
  can_generate_function_bodyt driver_program_can_generate_function_body,
  generate_function_bodyt driver_program_generate_function_body,
  message_handlert &message_handler)
  : goto_model(new goto_modelt()),
    symbol_table(goto_model->symbol_table),
    goto_functions(
      goto_model->goto_functions.function_map,
      language_files,
      symbol_table,
      [this] (
        const irep_idt &function_name,
        goto_functionst::goto_functiont &function,
        journalling_symbol_tablet &journalling_symbol_table) -> void
      {
        goto_model_functiont model_function(
          journalling_symbol_table,
          goto_model->goto_functions,
          function_name,
          function);
        this->post_process_function(model_function, *this);
      },
      driver_program_can_generate_function_body,
      driver_program_generate_function_body,
      message_handler),
    post_process_function(post_process_function),
    post_process_functions(post_process_functions),
    driver_program_can_generate_function_body(
      driver_program_can_generate_function_body),
    driver_program_generate_function_body(
      driver_program_generate_function_body),
    message_handler(message_handler)
{
  language_files.set_message_handler(message_handler);
}

lazy_goto_modelt::lazy_goto_modelt(lazy_goto_modelt &&other)
  : goto_model(std::move(other.goto_model)),
    symbol_table(goto_model->symbol_table),
    goto_functions(
      goto_model->goto_functions.function_map,
      language_files,
      symbol_table,
      [this] (
        const irep_idt &function_name,
        goto_functionst::goto_functiont &function,
        journalling_symbol_tablet &journalling_symbol_table) -> void
      {
        goto_model_functiont model_function(
          journalling_symbol_table,
          goto_model->goto_functions,
          function_name,
          function);
        this->post_process_function(model_function, *this);
      },
      other.driver_program_can_generate_function_body,
      other.driver_program_generate_function_body,
      other.message_handler),
    language_files(std::move(other.language_files)),
    post_process_function(other.post_process_function),
    post_process_functions(other.post_process_functions),
    message_handler(other.message_handler)
{
}
//! @endcond

void lazy_goto_modelt::initialize(
  const cmdlinet &cmdline,
  const optionst &options)
{
  messaget msg(message_handler);

  const std::vector<std::string> &files=cmdline.args;
  if(files.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "no program provided",
      "source file names",
      "one or more paths to a goto binary or a source file in a supported "
      "language");
  }

  std::vector<std::string> binaries, sources;
  binaries.reserve(files.size());
  sources.reserve(files.size());

  for(const auto &file : files)
  {
    if(is_goto_binary(file))
      binaries.push_back(file);
    else
      sources.push_back(file);
  }

  if(!sources.empty())
  {
    for(const auto &filename : sources)
    {
#ifdef _MSC_VER
      std::ifstream infile(widen(filename));
#else
      std::ifstream infile(filename);
#endif

      if(!infile)
      {
        throw system_exceptiont(
          "failed to open input file `" + filename + '\'');
      }

      language_filet &lf=add_language_file(filename);
      lf.language=get_language_from_filename(filename);

      if(lf.language==nullptr)
      {
        throw invalid_source_file_exceptiont(
          "failed to figure out type of file `" + filename + '\'');
      }

      languaget &language=*lf.language;
      language.set_message_handler(message_handler);
      language.set_language_options(options);

      msg.status() << "Parsing " << filename << messaget::eom;

      if(language.parse(infile, filename))
      {
        throw invalid_source_file_exceptiont("PARSING ERROR");
      }

      lf.get_modules();
    }

    msg.status() << "Converting" << messaget::eom;

    if(language_files.typecheck(symbol_table))
    {
      throw invalid_source_file_exceptiont("CONVERSION ERROR");
    }
  }

  for(const std::string &file : binaries)
  {
    msg.status() << "Reading GOTO program from file" << messaget::eom;

    if(read_object_and_link(file, *goto_model, message_handler))
    {
      source_locationt source_location;
      source_location.set_file(file);
      throw incorrect_goto_program_exceptiont(
        "failed to read/link goto model", source_location);
    }
  }

  bool binaries_provided_start =
    symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && cmdline.isset("function"))
  {
    // Rebuild the entry-point, using the language annotation of the
    // existing __CPROVER_start function:
    rebuild_lazy_goto_start_functiont rebuild_existing_start(
      options, *this, message_handler);
    entry_point_generation_failed=rebuild_existing_start();
  }
  else if(!binaries_provided_start)
  {
    // Unsure of the rationale for only generating stubs when there are no
    // GOTO binaries in play; simply mirroring old code in language_uit here.
    if(binaries.empty())
    {
      // Enable/disable stub generation for opaque methods
      bool stubs_enabled=cmdline.isset("generate-opaque-stubs");
      language_files.set_should_generate_opaque_method_stubs(stubs_enabled);
    }

    // Allow all language front-ends to try to provide the user-specified
    // (--function) entry-point, or some language-specific default:
    entry_point_generation_failed=
      language_files.generate_support_functions(symbol_table);
  }

  if(entry_point_generation_failed)
  {
    throw invalid_source_file_exceptiont("SUPPORT FUNCTION GENERATION ERROR");
  }

  // stupid hack
  config.set_object_bits_from_symbol_table(symbol_table);
}

/// Eagerly loads all functions from the symbol table.
void lazy_goto_modelt::load_all_functions() const
{
  symbol_tablet::symbolst::size_type table_size;
  symbol_tablet::symbolst::size_type new_table_size=symbol_table.symbols.size();
  do
  {
    table_size=new_table_size;

    // Find symbols that correspond to functions
    std::vector<irep_idt> fn_ids_to_convert;
    for(const auto &named_symbol : symbol_table.symbols)
    {
      if(named_symbol.second.is_function())
        fn_ids_to_convert.push_back(named_symbol.first);
    }

    for(const irep_idt &symbol_name : fn_ids_to_convert)
      goto_functions.ensure_function_loaded(symbol_name);

    // Repeat while new symbols are being added in case any of those are
    // stubbed functions. Even stubs can create new stubs while being
    // converted if they are special stubs (e.g. string functions)
    new_table_size=symbol_table.symbols.size();
  } while(new_table_size!=table_size);

  goto_model->goto_functions.compute_location_numbers();
}

bool lazy_goto_modelt::finalize()
{
  messaget msg(message_handler);
  journalling_symbol_tablet symbol_table=
    journalling_symbol_tablet::wrap(this->symbol_table);
  if(language_files.final(symbol_table))
  {
    msg.error() << "CONVERSION ERROR" << messaget::eom;
    return true;
  }
  for(const irep_idt &updated_symbol_id : symbol_table.get_updated())
  {
    if(symbol_table.lookup_ref(updated_symbol_id).is_function())
    {
      // Re-convert any that already exist
      goto_functions.unload(updated_symbol_id);
      goto_functions.ensure_function_loaded(updated_symbol_id);
    }
  }

  language_files.clear();

  return post_process_functions(*goto_model);
}

bool lazy_goto_modelt::can_produce_function(const irep_idt &id) const
{
  return goto_functions.can_produce_function(id);
}
