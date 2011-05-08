/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "symex_target_equation.h"
#include "slice.h"

/*******************************************************************\

   Class: symex_slicet

 Purpose:

\*******************************************************************/

class symex_slicet
{
public:
  void slice(symex_target_equationt &equation);

  void slice(symex_target_equationt &equation, 
             const expr_listt &expressions);

  void collect_open_variables(
    const symex_target_equationt &equation, 
    symbol_sett &open_variables);

protected:
  symbol_sett depends;
  
  void get_symbols(const exprt &expr);
  void get_symbols(const typet &type);

  void slice(symex_target_equationt::SSA_stept &SSA_step);
  void slice_assignment(symex_target_equationt::SSA_stept &SSA_step);
};

