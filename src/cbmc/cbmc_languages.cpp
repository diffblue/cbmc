/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "cbmc_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language_info.h>
#include <cpp/cpp_language_info.h>
#include <jsil/jsil_language_info.h>

void cbmc_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language_info);
  register_language(new_cpp_language_info);
  register_language(new_jsil_language_info);
}
