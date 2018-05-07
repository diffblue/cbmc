/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_instrument_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language_info.h>
#include <cpp/cpp_language_info.h>

void goto_instrument_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language_info);
  register_language(new_cpp_language_info);
}
