/*******************************************************************\

Module: Language Registration

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Language Registration

#include "jdiff_parse_options.h"

#include <langapi/mode.h>

#include <java_bytecode/java_bytecode_language.h>

void jdiff_parse_optionst::register_languages()
{
  register_language(new_java_bytecode_language);
}
