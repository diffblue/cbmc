/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_MODE_H
#define CPROVER_LANGAPI_MODE_H

#include <langapi/language_info.h>

#include <util/irep.h>

#include <memory> // unique_ptr

class languaget;
class namespacet;

std::unique_ptr<languaget> get_language_from_mode(const irep_idt &mode);

const language_infot &get_language_info_from_mode(const irep_idt &mode);

const irep_idt &
get_mode_from_identifier(const namespacet &ns, const irep_idt &identifier);

const language_infot &get_language_info_from_identifier(
  const namespacet &ns,
  const irep_idt &identifier);

std::unique_ptr<languaget>
get_language_from_identifier(const namespacet &ns, const irep_idt &identifier);

std::unique_ptr<languaget> get_language_from_filename(
  const std::string &filename);

std::unique_ptr<languaget> get_default_language();
const language_infot &get_default_language_info();

void clear_languages();
void register_language(language_info_factoryt);

#endif // CPROVER_LANGAPI_MODE_H
