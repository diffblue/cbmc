/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <context.h>

#include "symex_dereference_state.h"
#include "renaming_ns.h"

/*******************************************************************\

Function: symex_dereference_statet::dereference_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_dereference_statet::dereference_failure(
  const std::string &property,
  const std::string &msg,
  const guardt &guard)
{
}

/*******************************************************************\

Function: symex_dereference_statet::has_failed_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_dereference_statet::has_failed_symbol(
  const exprt &expr,
  const symbolt *&symbol)
{
  renaming_nst renaming_ns(goto_symex.ns, state);

  if(expr.id()==ID_symbol)
  {
    const symbolt &ptr_symbol=
      renaming_ns.lookup(to_symbol_expr(expr).get_identifier());

    const irep_idt &failed_symbol=
      ptr_symbol.type.get("#failed_symbol");    
      
    if(failed_symbol!="" &&
        !renaming_ns.lookup(failed_symbol, symbol))
    {
      symbolt sym=*symbol;
      symbolt *sym_ptr=0;
      sym.name=state.rename(sym.name, renaming_ns, goto_symex_statet::L1);
      goto_symex.new_context.move(sym, sym_ptr);
      symbol=sym_ptr;
      return true;
    }
  }
  
  return false;
}

/*******************************************************************\

Function: symex_dereference_statet::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_dereference_statet::get_value_set(
  const exprt &expr,
  value_setst::valuest &value_set)
{
  renaming_nst renaming_ns(goto_symex.ns, state);

  state.value_set.get_value_set(expr, value_set, renaming_ns);
  
  #if 0
  std::cout << "**************************\n";
  state.value_set.output(renaming_ns, std::cout);
  std::cout << "**************************\n";
  #endif
  
  #if 0
  std::cout << "E: " << from_expr(renaming_ns, "", expr) << std::endl;
  #endif
  
  #if 0
  std::cout << "**************************\n";
  for(value_setst::valuest::const_iterator it=value_set.begin();
      it!=value_set.end();
      it++)
    std::cout << from_expr(renaming_ns, "", *it) << std::endl;
  std::cout << "**************************\n";
  #endif
}

