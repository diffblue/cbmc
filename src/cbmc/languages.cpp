/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

#ifdef HAVE_CPP
#include <cpp/cpp_language.h>
#endif

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

#ifdef HAVE_JAVA_BYTECODE
#include <java_bytecode/java_bytecode_language.h>
#endif

#include "parseoptions.h"

/*******************************************************************\

Function: cbmc_parseoptionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parseoptionst::register_languages()
{
  register_language(new_ansi_c_language);
  
  #ifdef HAVE_CPP
  register_language(new_cpp_language);
  #endif
  
  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif
  
  #ifdef HAVE_JAVA_BYTECODE
  register_language(new_java_bytecode_language);
  #endif
}

