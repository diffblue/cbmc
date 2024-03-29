/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "cbmc_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <json-symtab-language/json_symtab_language.h>
#include <statement-list/statement_list_language.h>

void cbmc_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_statement_list_language);
  register_language(new_cpp_language);
  register_language(new_json_symtab_language);
}
