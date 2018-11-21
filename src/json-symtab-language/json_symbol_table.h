/*******************************************************************\

Module: JSON symbol table deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_TABLE_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_TABLE_H

class jsont;
class symbol_tablet;

void symbol_table_from_json(const jsont &, symbol_tablet &);

#endif
