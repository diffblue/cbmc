/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_RENAMING_NS_H
#define CPROVER_GOTO_SYMEX_RENAMING_NS_H

#include <namespace.h>

class renaming_nst:public namespacet
{
public:
  renaming_nst(
    const namespacet &_ns,
    class goto_symex_statet &_state):
    namespacet(_ns),
    state(_state)
  {
  }
   
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const
  {
    return namespacet::lookup(state.get_original_name(name), symbol);
  }
  
  const symbolt &lookup(const irep_idt &name) const
  {
    return namespacet::lookup(state.get_original_name(name));
  }
  
protected:
  class goto_symex_statet &state;
};
 
#endif
