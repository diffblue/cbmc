#ifndef OVERFLOW_INSTRUMENTER_H
#define OVERFLOW_INSTRUMENTER_H

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

#include <set>

class overflow_instrumentert {
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
  void add_overflow_checks(goto_programt::targett t, goto_programt::targetst &added);

 protected:
  void add_overflow_checks(goto_programt::targett t, const exprt &expr,
      goto_programt::targetst &added);

  void accumulate_overflow(goto_programt::targett t, const exprt &expr,
      goto_programt::targetst &added);

  goto_programt &program;
  symbol_tablet &symbol_table;
  const exprt &overflow_var;

  namespacet ns;
  std::set<int> checked;
};

#endif
