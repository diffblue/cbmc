/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_diff_languages.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

#include <java_bytecode/java_bytecode_language.h>

void goto_diff_languagest::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif

  register_language(new_java_bytecode_language);
}
