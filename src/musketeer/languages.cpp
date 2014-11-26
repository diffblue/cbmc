/*******************************************************************\

Module: Language Registration

Author:

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

#include "musketeer_parseoptions.h"

/*******************************************************************\

Function: goto_instrument_parseoptionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_fence_inserter_parseoptionst::register_languages()
{
  register_language(new_ansi_c_language);
}

