/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#ifndef CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H
#define CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H

#include <pointer-analysis/dereference_callback.h>

#include "goto_symex.h"

class symex_dereference_statet:
  public dereference_callbackt
{
public:
  symex_dereference_statet(
    goto_symext &_goto_symex,
    goto_symext::statet &_state):
    goto_symex(_goto_symex),
    state(_state)
  {
  }

protected:
  goto_symext &goto_symex;
  goto_symext::statet &state;

  virtual void get_value_set(
    const exprt &expr,
    value_setst::valuest &value_set);

  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H
