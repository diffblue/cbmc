/*******************************************************************\

Module: ANSI-C Linking

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// ANSI-C Linking

#ifndef CPROVER_LINKING_LINKING_DIAGNOSTICS_H
#define CPROVER_LINKING_LINKING_DIAGNOSTICS_H

#include <util/std_expr.h>
#include <util/symbol.h>

class message_handlert;
class namespacet;

class linking_diagnosticst
{
public:
  linking_diagnosticst(message_handlert &message_handler, namespacet &ns)
    : message_handler(message_handler), ns(ns)
  {
  }

  void error(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg);

  void warning(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg);

  void detailed_conflict_report(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const typet &type1,
    const typet &type2)
  {
    symbol_exprt conflict_path = symbol_exprt::typeless(ID_C_this);
    detailed_conflict_report_rec(
      old_symbol,
      new_symbol,
      type1,
      type2,
      10, // somewhat arbitrary limit
      conflict_path);
  }

protected:
  message_handlert &message_handler;
  const namespacet &ns;

  std::string
  type_to_string_verbose(const symbolt &symbol, const typet &type) const;

  std::string type_to_string_verbose(const symbolt &symbol) const
  {
    return type_to_string_verbose(symbol, symbol.type);
  }

  /// Returns true iff the conflict report on a particular branch of the tree of
  /// types was a definitive result, and not contingent on conflicts within a
  /// tag type.
  bool detailed_conflict_report_rec(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const typet &type1,
    const typet &type2,
    unsigned depth,
    exprt &conflict_path);
};

#endif // CPROVER_LINKING_LINKING_DIAGNOSTICS_H
