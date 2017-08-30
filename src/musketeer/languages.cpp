/*******************************************************************\

Module: Language Registration

Author:

\*******************************************************************/

/// \file
/// Language Registration

#include "musketeer_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

void goto_fence_inserter_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
}
