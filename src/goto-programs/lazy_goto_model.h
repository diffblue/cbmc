// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Model for lazy loading of functions

#ifndef CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H

#include <util/language_file.h>

#include "goto_model.h"
#include "lazy_goto_functions_map.h"
#include "goto_convert_functions.h"

class cmdlinet;
class optionst;

/// Model that holds partially loaded map of functions
class lazy_goto_modelt
{
public:
  typedef std::function<void(goto_model_functiont &function)>
    post_process_functiont;
  typedef std::function<bool(goto_modelt &goto_model)> post_process_functionst;

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

  /// Create a lazy_goto_modelt from a object that defines function/module pass
  /// handlers
  /// \param handler: An object that defines the handlers
  /// \param options: The options passed to process_goto_functions
  /// \param message_handler: The message_handler to use for logging
  /// \tparam THandler a type that defines methods process_goto_function and
  /// process_goto_functions
  template<typename THandler>
  static lazy_goto_modelt from_handler_object(
    THandler &handler,
    const optionst &options,
    message_handlert &message_handler)
  {
    return lazy_goto_modelt(
      [&handler] (goto_model_functiont &function)
      {
        handler.process_goto_function(function);
      },
      [&handler, &options] (goto_modelt &goto_model) -> bool
      {
        return handler.process_goto_functions(goto_model, options);
      },
      message_handler);
  }

  void initialize(const cmdlinet &cmdline);

  /// Eagerly loads all functions from the symbol table.
  void load_all_functions() const;

  void unload(const irep_idt &name) const { goto_functions.unload(name); }

  language_filet &add_language_file(const std::string &filename)
  {
    return language_files.add_file(filename);
  }

  /// The model returned here has access to the functions we've already
  /// loaded but is frozen in the sense that, with regard to the facility to
  /// load new functions, it has let it go.
  /// Before freezing the functions all module-level passes are run
  /// \param model: The lazy_goto_modelt to freeze
  /// \returns The frozen goto_modelt or an empty optional if freezing fails
  static std::unique_ptr<goto_modelt> process_whole_model_and_freeze(
    lazy_goto_modelt &&model)
  {
    if(model.finalize())
      return nullptr;
    return std::move(model.goto_model);
  }

private:
  std::unique_ptr<goto_modelt> goto_model;

public:
  /// Reference to symbol_table in the internal goto_model
  symbol_tablet &symbol_table;

private:
  const lazy_goto_functions_mapt<goto_programt> goto_functions;
  language_filest language_files;

  // Function/module processing functions
  const post_process_functiont post_process_function;
  const post_process_functionst post_process_functions;

  /// Logging helper field
  message_handlert &message_handler;

  bool finalize();
};

#endif // CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
