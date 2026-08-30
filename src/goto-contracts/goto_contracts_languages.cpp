/*******************************************************************\

Module: Language Registration

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_contracts_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

void goto_contracts_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}
