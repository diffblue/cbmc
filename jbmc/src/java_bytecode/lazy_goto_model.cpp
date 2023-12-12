/// Author: Diffblue Ltd.

/// \file
/// Model for lazy loading of functions

#include "lazy_goto_model.h"

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/journalling_symbol_table.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/read_goto_binary.h>

#include <langapi/mode.h>

#include "java_bytecode_language.h"

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <langapi/language.h>

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
      [this](
        const irep_idt &function_name,
        goto_functionst::goto_functiont &function,
        journalling_symbol_tablet &journalling_symbol_table) -> void {
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
}

lazy_goto_modelt::lazy_goto_modelt(lazy_goto_modelt &&other)
  : goto_model(std::move(other.goto_model)),
    symbol_table(goto_model->symbol_table),
    goto_functions(
      goto_model->goto_functions.function_map,
      language_files,
      symbol_table,
      [this](
        const irep_idt &function_name,
        goto_functionst::goto_functiont &function,
        journalling_symbol_tablet &journalling_symbol_table) -> void {
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

/// Performs initial symbol table and `language_filest` initialization from
/// a given commandline and parsed options. This is much the same as the
/// initial parsing phase of `initialize_goto_model`, except that all function
/// bodies may be left blank until `get_goto_function` is called for the first
/// time. This *must* be called before `get_goto_function` is called.
///
/// Whether they are in fact left blank depends on the language front-end
/// responsible for a particular function: it may be fully eager, in which case
/// only the `goto_convert` phase is performed lazily, or fully lazy, in which
/// case no function has a body until `get_goto_function` is called, or anything
/// in between. At the time of writing only Java-specific frontend programs use
/// `lazy_goto_modelt`, so only `java_bytecode_languaget` is relevant, and that
/// front-end supplies practically all methods lazily, apart from
/// `__CPROVER__start` and `__CPROVER_initialize`. In general check whether a
/// language implements `languaget::convert_lazy_method`; any method not handled
/// there must be populated eagerly. See `lazy_goto_modelt::get_goto_function`
/// for more detail.
/// \param files: source files and GOTO binaries to load
/// \param options: options to pass on to the language front-ends
void lazy_goto_modelt::initialize(
  const std::vector<std::string> &files,
  const optionst &options)
{
  messaget msg(message_handler);

  if(files.empty() && config.java.main_class.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "no program provided",
      "source file names",
      "one or more paths to a goto binary or a source file in a supported "
      "language");
  }

  std::list<std::string> binaries, sources;

  for(const auto &file : files)
  {
    if(is_goto_binary(file, message_handler))
      binaries.push_back(file);
    else
      sources.push_back(file);
  }

  if(sources.empty() && !config.java.main_class.empty())
  {
    // We assume it's Java.
    const std::string filename = "";
    language_filet &lf = add_language_file(filename);
    lf.language = get_language_from_mode(ID_java);
    CHECK_RETURN(lf.language != nullptr);

    languaget &language = *lf.language;
    language.set_language_options(options, message_handler);

    msg.status() << "Parsing ..." << messaget::eom;

    if(dynamic_cast<java_bytecode_languaget &>(language).parse(message_handler))
    {
      throw invalid_input_exceptiont("PARSING ERROR");
    }

    msg.status() << "Converting" << messaget::eom;

    if(language_files.typecheck(symbol_table, message_handler))
    {
      throw invalid_input_exceptiont("CONVERSION ERROR");
    }
  }
  else
  {
    initialize_from_source_files(
      sources, options, language_files, symbol_table, message_handler);
  }

  if(read_objects_and_link(binaries, *goto_model, message_handler))
    throw incorrect_goto_program_exceptiont{"failed to read/link goto model"};

  set_up_custom_entry_point(
    language_files,
    symbol_table,
    [this](const irep_idt &id) { return goto_functions.unload(id); },
    options,
    false,
    message_handler);

  // stupid hack
  config.set_object_bits_from_symbol_table(symbol_table);
}

/// Eagerly loads all functions from the symbol table.
void lazy_goto_modelt::load_all_functions() const
{
  symbol_tablet::symbolst::size_type table_size;
  symbol_tablet::symbolst::size_type new_table_size =
    symbol_table.symbols.size();
  do
  {
    table_size = new_table_size;

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
    new_table_size = symbol_table.symbols.size();
  } while(new_table_size != table_size);

  goto_model->goto_functions.compute_location_numbers();
}

bool lazy_goto_modelt::finalize()
{
  messaget msg(message_handler);
  journalling_symbol_tablet j_symbol_table =
    journalling_symbol_tablet::wrap(symbol_table);
  if(language_files.final(j_symbol_table))
  {
    msg.error() << "CONVERSION ERROR" << messaget::eom;
    return true;
  }
  for(const irep_idt &updated_symbol_id : j_symbol_table.get_updated())
  {
    if(j_symbol_table.lookup_ref(updated_symbol_id).is_function())
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
