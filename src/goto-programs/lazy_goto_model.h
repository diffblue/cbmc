// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Model for lazy loading of functions

#ifndef CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H

#include <util/language_file.h>

#include "goto_model.h"
#include "goto_convert_functions.h"

class cmdlinet;


/// Model that holds partially loaded map of functions
class lazy_goto_modelt
{
private:
  std::unique_ptr<goto_modelt> goto_model;

public:
  language_filest language_files;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

public:
  explicit lazy_goto_modelt(message_handlert &message_handler);

  lazy_goto_modelt(lazy_goto_modelt &&other);

  lazy_goto_modelt &operator=(lazy_goto_modelt &&other)
  {
    goto_model = std::move(other.goto_model);
    language_files = std::move(other.language_files);
    return *this;
  }

public:
  void initialize(const cmdlinet &cmdline);

  /// Eagerly loads all functions from the symbol table.
  void load_all_functions();

  /// The model returned here has access to the functions we've already
  /// loaded but is frozen in the sense that, with regard to the facility to
  /// load new functions, it has let it go.
  /// \param model: The lazy_goto_modelt to freeze
  /// \returns The frozen goto_modelt or an empty optional if freezing fails
  static std::unique_ptr<goto_modelt> freeze(lazy_goto_modelt &&model)
  {
    return std::move(model.goto_model);
  }
};

#endif // CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
