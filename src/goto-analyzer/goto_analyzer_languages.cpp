/*******************************************************************\

Module: Language Registration

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_analyzer_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#ifdef HAVE_JSIL
#  include <jsil/jsil_language.h>
#endif

void goto_analyzer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

#ifdef HAVE_JSIL
  register_language(new_jsil_language);
#endif
}
