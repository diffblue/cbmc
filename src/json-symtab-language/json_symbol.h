/*******************************************************************\

Module: JSON symbol deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_H

#include <util/symbol.h>

class jsont;

symbolt symbol_from_json(const jsont &);

#endif
