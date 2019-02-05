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

/// Callback object that \ref goto_symext::dereference_rec provides to
/// \ref value_set_dereferencet to provide value sets (from goto-symex's
/// working value set) and retrieve or create failed symbols on demand.
/// For details of symex-dereference's operation see
/// \ref goto_symext::dereference
class symex_dereference_statet:
  public dereference_callbackt
{
public:
  symex_dereference_statet(
    const goto_symext &_goto_symex,
    goto_symext::statet &_state)
    : goto_symex(_goto_symex), state(_state)
  {
  }

protected:
  const goto_symext &goto_symex;
  goto_symext::statet &state;

  void get_value_set(const exprt &expr, value_setst::valuest &value_set)
    const override;

  bool get_or_create_failed_symbol(const exprt &expr, const symbolt *&symbol)
    override;
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H
