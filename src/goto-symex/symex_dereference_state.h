/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <pointer-analysis/dereference.h>

#include "goto_symex.h"

/*******************************************************************\

   Class: symex_dereference_statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

  virtual void dereference_failure(
    const std::string &property,
    const std::string &msg,
    const guardt &guard);
          
  virtual void get_value_set(
    const exprt &expr,
    value_setst::valuest &value_set);

  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol);
};

