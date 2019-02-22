/*******************************************************************\

Module: Symbol Analyzer

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

// clang-format off
#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
// clang-format on

#ifndef CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#define CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H

#include <map>
#include <string>

#include "gdb_api.h"

#include <ansi-c/expr2c_class.h>

#include <util/allocate_objects.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

class gdb_apit;
class exprt;
class source_locationt;

class symbol_analyzert
{
public:
  symbol_analyzert(const symbol_tablet &symbol_table, gdb_apit &gdb_api);

  void analyze_symbols(const std::vector<std::string> &symbols);

  std::string get_snapshot_as_c_code();
  symbol_tablet get_snapshot_as_symbol_table();

  using pointer_valuet = gdb_apit::pointer_valuet;

private:
  gdb_apit &gdb_api;
  symbol_tablet symbol_table;
  const namespacet ns;
  expr2ct c_converter;
  allocate_objectst allocate_objects;

  std::vector<std::pair<exprt, exprt>> assignments;

  std::map<exprt, std::string> outstanding_assignments;
  std::map<std::string, exprt> values;

  void analyze_symbol(const std::string &symbol_name);

  void add_assignment(const exprt &lhs, const exprt &value);

  exprt get_array_value(
    const exprt &expr,
    const exprt &array,
    const source_locationt &location);

  exprt get_expr_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  exprt get_struct_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  exprt get_pointer_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  exprt get_non_char_pointer_value(
    const exprt &expr,
    const std::string memory_location,
    const source_locationt &location);

  exprt get_char_pointer_value(
    const exprt &expr,
    const std::string &memory_location,
    const source_locationt &location);

  void process_outstanding_assignments();
};

#endif // CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#endif
