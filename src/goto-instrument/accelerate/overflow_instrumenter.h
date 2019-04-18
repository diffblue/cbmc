/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_OVERFLOW_INSTRUMENTER_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_OVERFLOW_INSTRUMENTER_H

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

#include <set>

#include "cone_of_influence.h"

class overflow_instrumentert
{
 public:
  overflow_instrumentert(goto_programt &_program,
      const exprt &_overflow_var,
      symbol_tablet &_symbol_table) :
    program(_program),
    symbol_table(_symbol_table),
    overflow_var(_overflow_var),
    ns(symbol_table)
  {
  }

  void add_overflow_checks();
  void add_overflow_checks(goto_programt::targett t);
  void add_overflow_checks(
    goto_programt::targett t,
    goto_programt::targetst &added);

  void overflow_expr(const exprt &expr, expr_sett &cases);
  void overflow_expr(const exprt &expr, exprt &overflow);

 protected:
  void add_overflow_checks(goto_programt::targett t, const exprt &expr,
      goto_programt::targetst &added);

  void accumulate_overflow(goto_programt::targett t, const exprt &expr,
      goto_programt::targetst &added);

  void fix_types(binary_exprt &overflow);

  goto_programt &program;
  symbol_tablet &symbol_table;
  const exprt &overflow_var;

  namespacet ns;
  std::set<unsigned> checked;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_OVERFLOW_INSTRUMENTER_H
