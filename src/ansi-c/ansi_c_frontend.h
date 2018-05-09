/*******************************************************************\

Module: ANSI-C Language Frontend

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_ANSI_C_ANSI_C_FRONTEND_H
#define CPROVER_ANSI_C_ANSI_C_FRONTEND_H

#include <goto-programs/goto_frontend.h>
#include <goto-programs/goto_functions.h>

class ansi_c_frontendt : public goto_frontendt
{
public:
  const goto_functiont &&make_function(const irep_idt &) override;
  const symbolt &get_symbol(const irep_idt &) override;

protected:
  symbol_tablet symbol_table;
};

#endif
