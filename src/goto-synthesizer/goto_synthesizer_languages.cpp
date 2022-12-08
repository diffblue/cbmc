/*******************************************************************\
Module: Language Registration
Author: Qinheping Hu
\*******************************************************************/

/// \file
/// Language Registration

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <langapi/mode.h>

#include "goto_synthesizer_parse_options.h"

void goto_synthesizer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}
