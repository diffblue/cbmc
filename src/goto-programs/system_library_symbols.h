/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H
#define CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H

#include <list>
#include <set>
#include <util/irep.h>

class symbolt;

class system_library_symbolst
{
public:
  system_library_symbolst();

  bool is_symbol_internal_symbol(
    const symbolt &symbol,
    std::set<irep_idt> &out_system_headers) const;

private:
  void init_system_library_map();

  void add_to_system_library(
    irep_idt header_file,
    std::list<irep_idt> symbols);

  std::map<irep_idt, irep_idt> system_library_map;
};

#endif // CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H
