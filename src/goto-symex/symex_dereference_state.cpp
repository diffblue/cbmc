/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "symex_dereference_state.h"

#include <util/symbol_table.h>

/// Get or create a failed symbol for the given pointer-typed expression. These
/// are used as placeholders when dereferencing expressions that are illegal to
/// dereference, such as null pointers. The \ref add_failed_symbols pass must
/// have been run for this to do anything useful;  it annotates a pointer-typed
/// symbol `p` with an `ID_C_failed_symbol` comment, which we then clone on
/// demand due to L1 renaming.
///
/// For example, if \p expr is `p` and it has an `ID_C_failed_symbol` `p$object`
/// (the naming convention used by `add_failed_symbols`), and the latest L1
/// renaming of `p` is `p!2@4`, then we will create `p$object!2@4` if it doesn't
/// already exist.
///
/// \param expr: expression to get or create a failed symbol for
/// \return pointer to the failed symbol for \p expr, or nullptr if none
const symbolt *
symex_dereference_statet::get_or_create_failed_symbol(const exprt &expr)
{
  if(is_ssa_expr(expr))
  {
    const ssa_exprt &ssa_expr=to_ssa_expr(expr);
    if(ssa_expr.get_original_expr().id()!=ID_symbol)
      return nullptr;

    const symbolt &ptr_symbol=
      ns.lookup(to_ssa_expr(expr).get_object_name());

    const irep_idt &failed_symbol = ptr_symbol.type.get(ID_C_failed_symbol);

    const symbolt *symbol;
    if(!failed_symbol.empty() && !ns.lookup(failed_symbol, symbol))
    {
      symbolt sym=*symbol;
      symbolt *sym_ptr=nullptr;
      const ssa_exprt sym_expr =
        state.rename_ssa<L1>(ssa_exprt{sym.symbol_expr()}, ns).get();
      sym.name = sym_expr.get_identifier();
      state.symbol_table.move(sym, sym_ptr);
      return sym_ptr;
    }
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &ptr_symbol=
      ns.lookup(to_symbol_expr(expr).get_identifier());

    const irep_idt &failed_symbol = ptr_symbol.type.get(ID_C_failed_symbol);

    const symbolt *symbol;
    if(!failed_symbol.empty() && !ns.lookup(failed_symbol, symbol))
    {
      symbolt sym=*symbol;
      symbolt *sym_ptr=nullptr;
      const ssa_exprt sym_expr =
        state.rename_ssa<L1>(ssa_exprt{sym.symbol_expr()}, ns).get();
      sym.name = sym_expr.get_identifier();
      state.symbol_table.move(sym, sym_ptr);
      return sym_ptr;
    }
  }

  return nullptr;
}

/// Just forwards a value-set query to `state.value_set`
std::vector<exprt>
symex_dereference_statet::get_value_set(const exprt &expr) const
{
  return state.value_set.get_value_set(expr, ns);
}
