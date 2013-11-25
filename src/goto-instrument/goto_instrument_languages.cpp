/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

#include "goto_instrument_parseoptions.h"

/*******************************************************************\

Function: goto_instrument_parseoptionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_instrument_parseoptionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  
  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif
}

