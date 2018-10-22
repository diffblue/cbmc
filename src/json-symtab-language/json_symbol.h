/*******************************************************************\

Module: JSON symbol deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_JSON_SYMBOL_H
#define CPROVER_UTIL_JSON_SYMBOL_H

#include <util/json.h>
#include <util/symbol.h>

symbolt symbol_from_json(const jsont &);

#endif
