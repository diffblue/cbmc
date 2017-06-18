/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_MODE_H
#define CPROVER_LANGAPI_MODE_H

#include <util/irep.h>

class languaget;

languaget *get_language_from_mode(const irep_idt &mode);
languaget *get_language_from_filename(const std::string &filename);
languaget *get_default_language();

using language_factoryt = languaget *(*)();
void register_language(language_factoryt factory);

#endif // CPROVER_LANGAPI_MODE_H
