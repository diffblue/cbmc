/*******************************************************************\

Module: Get goto model

Author: Daniel Poetzl

\*******************************************************************/

#include "get_goto_model_from_c.h"

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert_functions.h>

#include <langapi/language_file.h>
#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/symbol_table.h>

#include <testing-utils/message.h>

goto_modelt get_goto_model_from_c(std::istream &in)
{
  {
    const bool has_language = get_language_from_mode(ID_C) != nullptr;

    if(!has_language)
    {
      register_language(new_ansi_c_language);
    }
  }

  {
    cmdlinet cmdline;

    config = configt{};
    config.main = std::string("main");
    config.set(cmdline);
  }

  language_filest language_files;
  language_files.set_message_handler(null_message_handler);

  language_filet &language_file = language_files.add_file("");

  language_file.language = get_language_from_mode(ID_C);
  CHECK_RETURN(language_file.language);

  languaget &language = *language_file.language;
  language.set_message_handler(null_message_handler);

  {
    const bool error = language.parse(in, "");

    if(error)
      throw invalid_input_exceptiont("parsing failed");
  }

  language_file.get_modules();

  goto_modelt goto_model;

  {
    const bool error = language_files.typecheck(goto_model.symbol_table);

    if(error)
      throw invalid_input_exceptiont("typechecking failed");
  }

  {
    const bool error =
      language_files.generate_support_functions(goto_model.symbol_table);

    if(error)
      throw invalid_input_exceptiont("support function generation failed");
  }

  goto_convert(
    goto_model.symbol_table, goto_model.goto_functions, null_message_handler);

  return goto_model;
}

goto_modelt get_goto_model_from_c(const std::string &code)
{
  std::istringstream in(code);
  return get_goto_model_from_c(in);
}
