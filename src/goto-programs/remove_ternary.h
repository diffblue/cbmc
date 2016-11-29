/*******************************************************************\

Module: Remove function returns

Author: Daniel Kroening

Date:   September 2009

\*******************************************************************/

#ifndef CPROVER_REMOVE_TERNARY_H
#define CPROVER_REMOVE_TERNARY_H

#include <goto-programs/goto_model.h>

class remove_ternaryt
{
public:
  explicit remove_ternaryt(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
  {
  }

  void operator()(goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;

  unsigned int replaced = 0;

  void replace_ternary(
      goto_programt &goto_program,
      goto_programt::instructionst::iterator &i_it,
          exprt &expr,
          bool lhs);

  void contains_ternary(exprt &expr, bool &contains);

  bool contains_ternary(exprt &expr);
};

void remove_ternary(symbol_tablet &, goto_functionst &);

void remove_ternary(goto_modelt &);

#endif
