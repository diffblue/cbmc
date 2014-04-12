#ifndef SCRATCH_PROGRAM_H
#define SCRATCH_PROGRAM_H

#include <string>

#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <solvers/smt2/smt2_dec.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "path.h"

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
      satcheck(new satcheckt),
      satchecker(ns, *satcheck),
      z3(ns, "accelerate", "", "", smt2_dect::Z3),

      // XXX Z3 appears to be much faster than minisat... investigate
      checker(&z3)
  {
  }

  ~scratch_programt() {
    delete satcheck;
  }

  symbolt fresh_symbol(string base, typet type);
  void append(goto_programt::instructionst &instructions);
  void append(goto_programt &program);
  void append_path(patht &path);
  void append_loop(goto_programt &program, goto_programt::targett loop_header);

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
  symex_target_equationt equation;
  goto_symext symex;

  propt *satcheck;
  bv_pointerst satchecker;
  smt2_dect z3;
  prop_convt *checker;
};

#endif // SCRATCH_PROGRAM_H
