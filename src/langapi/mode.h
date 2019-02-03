/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_MODE_H
#define CPROVER_LANGAPI_MODE_H

#include <util/irep.h>

#include <memory> // unique_ptr

class languaget;
class namespacet;

std::unique_ptr<languaget> get_language_from_mode(const irep_idt &mode);
const irep_idt &
get_mode_from_identifier(const namespacet &ns, const irep_idt &identifier);
std::unique_ptr<languaget>
get_language_from_identifier(const namespacet &ns, const irep_idt &identifier);
std::unique_ptr<languaget> get_language_from_filename(
  const std::string &filename);
std::unique_ptr<languaget> get_default_language();

typedef std::unique_ptr<languaget> (*language_factoryt)();
void register_language(language_factoryt factory);

#endif // CPROVER_LANGAPI_MODE_H
