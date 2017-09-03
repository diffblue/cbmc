/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley

\*******************************************************************/

/// \file
/// Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H
#define CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H

#include <list>
#include <set>
#include <string>
#include <util/irep.h>
#include <util/type.h>

class symbolt;
class typet;

class system_library_symbolst
{
public:
  system_library_symbolst();

  bool is_symbol_internal_symbol(
    const symbolt &symbol,
    std::set<std::string> &out_system_headers) const;

  bool is_type_internal(
    const typet &type,
    std::set<std::string> &out_system_headers) const;

  void set_use_all_headers(bool use)
  {
    use_all_headers=use;
  }

private:
  void init_system_library_map();

  void add_to_system_library(
    irep_idt header_file,
    std::list<irep_idt> symbols);

  std::map<irep_idt, irep_idt> system_library_map;
  bool use_all_headers;
};

#endif // CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H
