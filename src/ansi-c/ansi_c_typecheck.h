/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_TYPECHECK_H
#define CPROVER_ANSI_C_TYPECHECK_H

#include <ansi-c/c_typecheck_base.h>

#include "ansi_c_parse_tree.h"

bool ansi_c_typecheck(
  ansi_c_parse_treet &parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler);

bool ansi_c_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class ansi_c_typecheckt:public c_typecheck_baset
{
public:
  ansi_c_typecheckt(
    ansi_c_parse_treet &_parse_tree,
    contextt &_context,
    const std::string &_module,
    message_handlert &_message_handler):
    c_typecheck_baset(_context, _module, _message_handler),
    parse_tree(_parse_tree)
  {
  }

  ansi_c_typecheckt(
    ansi_c_parse_treet &_parse_tree,
    contextt &_context1,
    const contextt &_context2,
    const std::string &_module,
    message_handlert &_message_handler):
    c_typecheck_baset(_context1, _context2,
                      _module, _message_handler),
    parse_tree(_parse_tree)
  {
  }

  virtual ~ansi_c_typecheckt() { }

  virtual void typecheck();

protected:
  ansi_c_parse_treet &parse_tree;
};

#endif
