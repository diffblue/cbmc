/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley

\*******************************************************************/

/// \file
/// Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H
#define CPROVER_GOTO_PROGRAMS_SYSTEM_LIBRARY_SYMBOLS_H

#include <list>
#include <map>
#include <set>
#include <string>
#include <util/irep.h>

class symbolt;
class typet;

class system_library_symbolst
{
public:
  explicit system_library_symbolst(bool init);

  system_library_symbolst():
    system_library_symbolst(true) // NOLINT(runtime/explicit)
  {
  }

  bool is_symbol_internal_symbol(
    const symbolt &symbol,
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
