/*******************************************************************\

Module: Language Registration

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_cc_mode.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language_info.h>
#include <cpp/cpp_language_info.h>
#include <jsil/jsil_language_info.h>

void goto_cc_modet::register_languages()
{
  register_language(new_ansi_c_language_info);
  register_language(new_cpp_language_info);
  register_language(new_jsil_language_info);
}
