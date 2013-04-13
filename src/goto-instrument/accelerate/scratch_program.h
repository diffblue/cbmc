#ifndef SCRATCH_PROGRAM_H
#define SCRATCH_PROGRAM_H

#include <string>

#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <solvers/smt2/smt2_dec.h>

using namespace std;

class scratch_programt : public goto_programt {
 public:
  scratch_programt(const symbol_tablet &_symbol_table) :
      constant_propagation(true),
      symbol_table(_symbol_table),
      shadow_symbol_table(_symbol_table),
      ns(shadow_symbol_table),
      equation(ns),
      symex(ns, shadow_symbol_table, equation),
      checker(ns, "scratch", "", "AUFBV", smt2_dect::Z3)
  {
  }

  symbolt fresh_symbol(string base);
  void append(goto_programt::instructionst &instructions);

  targett assign(const exprt &lhs, const exprt &rhs);
  targett assume(const exprt &guard);

  bool check_sat();
  exprt eval(exprt &e);

  void fix_types();

  bool constant_propagation;

 protected:

  goto_symex_statet symex_state;
  goto_functionst functions;
  const symbol_tablet &symbol_table;
  symbol_tablet shadow_symbol_table;
  const namespacet ns;
  smt2_dect checker;
  symex_target_equationt equation;
  goto_symext symex;

};

#endif // SCRATCH_PROGRAM_H
