/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "goto_diff_languages.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language_info.h>

#include <cpp/cpp_language_info.h>

#include <java_bytecode/java_bytecode_language_info.h>

void goto_diff_languagest::register_languages()
{
  register_language(new_ansi_c_language_info);
  register_language(new_cpp_language_info);
  register_language(new_java_bytecode_language_info);
}
