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
#include <jsil/jsil_language.h>

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

void goto_cc_modet::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  register_language(new_jsil_language);

  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif
}
