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
class message_handlert;

std::unique_ptr<languaget> get_language_from_mode(const irep_idt &mode);
std::unique_ptr<languaget>
get_language_from_mode(const irep_idt &mode, message_handlert &);
const irep_idt &
get_mode_from_identifier(const namespacet &, const irep_idt &identifier);
std::unique_ptr<languaget>
get_language_from_identifier(const namespacet &, const irep_idt &identifier);
std::unique_ptr<languaget> get_language_from_identifier(
  const namespacet &,
  const irep_idt &identifier,
  message_handlert &);
std::unique_ptr<languaget> get_language_from_filename(
  const std::string &filename);
std::unique_ptr<languaget>
get_language_from_filename(const std::string &filename, message_handlert &);
std::unique_ptr<languaget> get_default_language();
std::unique_ptr<languaget> get_default_language(message_handlert &);

typedef std::unique_ptr<languaget> (*language_factoryt)(message_handlert &);
void register_language(language_factoryt factory);

#endif // CPROVER_LANGAPI_MODE_H
