/*******************************************************************\

Module: JSON symbol table deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_JSON_SYMBOL_TABLE_H
#define CPROVER_UTIL_JSON_SYMBOL_TABLE_H

#include <util/json.h>
#include <util/symbol_table.h>

void symbol_table_from_json(const jsont &, symbol_tablet &);

#endif
