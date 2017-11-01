/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#ifndef CPROVER_GOTO_SYMEX_SYMEX_SLICE_CLASS_H
#define CPROVER_GOTO_SYMEX_SYMEX_SLICE_CLASS_H

#include "symex_target_equation.h"
#include "slice.h"

class symex_slicet : SSA_visitor
{
public:
  void slice(symex_target_equationt &equation);

  void slice(symex_target_equationt &equation,
             const expr_listt &expressions);

  void collect_open_variables(
    const symex_target_equationt &equation,
    symbol_sett &open_variables);

  void visit(SSA_assertt &x);
  void visit(SSA_assumet &x);
  void visit(SSA_assignmentt &x);
  void visit(SSA_gotot &x);
  void visit(SSA_constraintt &x);
  void visit(SSA_locationt &x);
  void visit(SSA_outputt &x);
  void visit(SSA_declt &x);
  void visit(SSA_function_callt &x);
  void visit(SSA_function_returnt &x);
  void visit(SSA_shared_readt &x);
  void visit(SSA_shared_writet &x);
  void visit(SSA_spawnt &x);
  void visit(SSA_memory_barriert &x);
  void visit(SSA_atomic_begint &x);
  void visit(SSA_atomic_endt &x);
  void visit(SSA_inputt &x);

protected:
  symbol_sett depends;

  void get_symbols(const exprt &expr);
  void get_symbols(const typet &type);

  void slice(symex_target_equationt::SSA_stept &SSA_step);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_SLICE_CLASS_H
