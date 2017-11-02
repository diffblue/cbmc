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

class symex_slicet final {
public:
  void slice(symex_target_equationt &equation);

  void slice(symex_target_equationt &equation,
             const expr_listt &expressions);

  void collect_open_variables(
    const symex_target_equationt &equation,
    symbol_sett &open_variables);

private:
  symbol_sett depends_;

  void slice(symex_target_equationt::SSA_stept &SSA_step);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_SLICE_CLASS_H
