// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Model for lazy loading of functions

#ifndef CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H

#include <util/language_file.h>
#include <util/exit_codes.h>

#include "goto_model.h"
#include "lazy_goto_functions_map.h"
#include "goto_convert_functions.h"

class cmdlinet;
class optionst;


/// Model that holds partially loaded map of functions
class lazy_goto_modelt
{
public:
  typedef std::function<void(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &function,
    symbol_tablet &symbol_table)> post_process_functiont;
  typedef std::function<bool(goto_modelt &goto_model)> post_process_functionst;

private:
  std::unique_ptr<goto_modelt> goto_model;

public:
  language_filest language_files;
  symbol_tablet &symbol_table;
  const lazy_goto_functions_mapt<goto_programt> goto_functions;

private:
  const post_process_functionst post_process_functions;

public:
  explicit lazy_goto_modelt(
    post_process_functiont post_process_function,
    post_process_functionst post_process_functions,
    message_handlert &message_handler);

  lazy_goto_modelt(lazy_goto_modelt &&other);

  lazy_goto_modelt &operator=(lazy_goto_modelt &&other)
  {
    goto_model = std::move(other.goto_model);
    language_files = std::move(other.language_files);
    return *this;
  }

  template<typename THandler>
  static lazy_goto_modelt from_handler_object(
    THandler &handler,
    const optionst &options,
    message_handlert &message_handler);

public:
  void initialize(const cmdlinet &cmdline);

private:
  static bool is_function_symbol(const symbolt &symbol)
  { return !symbol.is_type && !symbol.is_macro && symbol.type.id()==ID_code; }

public:
  /// Eagerly loads all functions from the symbol table.
  void load_all_functions();

  /// The model returned here has access to the functions we've already
  /// loaded but is frozen in the sense that, with regard to the facility to
  /// load new functions, it has let it go.
  /// \param model: The lazy_goto_modelt to freeze
  /// \returns The frozen goto_modelt or an empty optional if freezing fails
  static std::unique_ptr<goto_modelt> freeze(lazy_goto_modelt &&model)
  {
    if(!model.freeze())
      return nullptr;
    return std::move(model.goto_model);
  }

private:
  bool freeze();
};


template<typename THandler>
lazy_goto_modelt lazy_goto_modelt::from_handler_object(
  THandler &handler,
  const optionst &options,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  return lazy_goto_modelt(
    [&handler, &msg] (
      const irep_idt &function_name,
      goto_functionst::goto_functiont &function,
      symbol_tablet &symbol_table) -> void
    {
      try
      {
        handler.process_goto_function(function_name, function, symbol_table);
      }
      catch(const char *e)
      {
        msg.error() << "process_goto_function: " << e << messaget::eom;
        throw;
      }
      catch(const std::string &e)
      {
        msg.error() << "process_goto_function: " << e << messaget::eom;
        throw;
      }
      catch(int e)
      {
        msg.error()
          << "process_goto_function: Numeric exception : " << e
          << messaget::eom;
        throw;
      }
      catch(const std::bad_alloc &)
      {
        msg.error() << "process_goto_function: Out of memory" << messaget::eom;
        exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
      }
    },
    [&handler, &options, &msg] (goto_modelt &goto_model) -> bool
    {
      try
      {
        return handler.process_goto_functions(goto_model, options);
      }
      catch(const char *e)
      {
        msg.error() << "process_goto_functions: " << e << messaget::eom;
      }
      catch(const std::string &e)
      {
        msg.error() << "process_goto_functions: " << e << messaget::eom;
      }
      catch(int e)
      {
        msg.error()
          << "process_goto_functions: Numeric exception : " << e
          << messaget::eom;
      }
      catch(const std::bad_alloc &)
      {
        msg.error()
          << "process_goto_functions: Out of memory" << messaget::eom;
        exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
      }
      return true;
    },
    message_handler);
}

#endif // CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
