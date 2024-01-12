/*******************************************************************\

Module: Language Registration

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_cc_mode.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

void goto_cc_modet::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}
