/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Registration

#include "cbmc_parse_options.h"

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <json-symtab-language/json_symtab_language.h>

#ifdef HAVE_JSIL
#include <jsil/jsil_language.h>
#endif

void cbmc_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  register_language(new_json_symtab_language);

#ifdef HAVE_JSIL
  register_language(new_jsil_language);
#endif
}
