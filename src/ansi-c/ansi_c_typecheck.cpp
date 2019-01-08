/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "ansi_c_typecheck.h"

void ansi_c_typecheckt::typecheck()
{
  start_typecheck_code();

  for(auto &item : parse_tree.items)
    typecheck_declaration(item);
}

bool ansi_c_typecheck(
  ansi_c_parse_treet &ansi_c_parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parse_tree, symbol_table, module, message_handler);
  return ansi_c_typecheck.typecheck_main();
}

bool ansi_c_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  const unsigned errors_before=
    message_handler.get_message_count(messaget::M_ERROR);

  symbol_tablet symbol_table;
  ansi_c_parse_treet ansi_c_parse_tree;

  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parse_tree, symbol_table,
    ns.get_symbol_table(), "", message_handler);

  try
  {
    ansi_c_typecheck.typecheck_expr(expr);
  }

  catch(int)
  {
    ansi_c_typecheck.error();
  }

  catch(const char *e)
  {
    ansi_c_typecheck.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    ansi_c_typecheck.error() << e << messaget::eom;
  }

  return message_handler.get_message_count(messaget::M_ERROR)!=errors_before;
}
