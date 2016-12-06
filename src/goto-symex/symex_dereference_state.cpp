/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol_table.h>

#include "symex_dereference_state.h"

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
  const namespacet &ns=goto_symex.ns;

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    const ssa_exprt &ssa_expr=to_ssa_expr(expr);
    if(ssa_expr.get_original_expr().id()!=ID_symbol)
      return false;

    const symbolt &ptr_symbol=
      ns.lookup(to_ssa_expr(expr).get_object_name());

    const irep_idt &failed_symbol=
      ptr_symbol.type.get("#failed_symbol");

    if(failed_symbol!="" &&
        !ns.lookup(failed_symbol, symbol))
    {
      symbolt sym=*symbol;
      symbolt *sym_ptr=0;
      symbol_exprt sym_expr=sym.symbol_expr();
      state.rename(sym_expr, ns, goto_symex_statet::L1);
      sym.name=to_ssa_expr(sym_expr).get_identifier();
      goto_symex.new_symbol_table.move(sym, sym_ptr);
      symbol=sym_ptr;
      return true;
    }
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &ptr_symbol=
      ns.lookup(to_symbol_expr(expr).get_identifier());

    const irep_idt &failed_symbol=
      ptr_symbol.type.get("#failed_symbol");

    if(failed_symbol!="" &&
        !ns.lookup(failed_symbol, symbol))
    {
      symbolt sym=*symbol;
      symbolt *sym_ptr=0;
      symbol_exprt sym_expr=sym.symbol_expr();
      state.rename(sym_expr, ns, goto_symex_statet::L1);
      sym.name=to_ssa_expr(sym_expr).get_identifier();
      goto_symex.new_symbol_table.move(sym, sym_ptr);
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
  state.value_set.get_value_set(expr, value_set, goto_symex.ns);

  #if 0
  std::cout << "**************************\n";
  state.value_set.output(goto_symex.ns, std::cout);
  std::cout << "**************************\n";
  #endif

  #if 0
  std::cout << "E: " << from_expr(goto_symex.ns, "", expr) << std::endl;
  #endif

  #if 0
  std::cout << "**************************\n";
  for(value_setst::valuest::const_iterator it=value_set.begin();
      it!=value_set.end();
      it++)
    std::cout << from_expr(goto_symex.ns, "", *it) << std::endl;
  std::cout << "**************************\n";
  #endif
}
