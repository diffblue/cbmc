/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H

#include <memory>
#include <string>

#include <util/make_unique.h>
#include <util/message.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/path_storage.h>
#include <goto-symex/symex_target_equation.h>

#include <solvers/smt2/smt2_dec.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "path.h"

class scratch_programt:public goto_programt
{
public:
  scratch_programt(symbol_tablet &_symbol_table, message_handlert &mh)
    : constant_propagation(true),
      symbol_table(_symbol_table),
      symex_symbol_table(),
      ns(symbol_table, symex_symbol_table),
      equation(),
      path_storage(),
      options(get_default_options()),
      symex(mh, symbol_table, equation, options, path_storage),
      satcheck(util_make_unique<satcheckt>()),
      satchecker(ns, *satcheck),
      z3(ns, "accelerate", "", "", smt2_dect::solvert::Z3),
      checker(&z3) // checker(&satchecker)
  {
  }

  void append(goto_programt::instructionst &instructions);
  void append(goto_programt &program);
  void append_path(patht &path);
  void append_loop(goto_programt &program, goto_programt::targett loop_header);

  targett assign(const exprt &lhs, const exprt &rhs);
  targett assume(const exprt &guard);

  bool check_sat(bool do_slice);

  bool check_sat()
  {
    return check_sat(true);
  }

  exprt eval(const exprt &e);

  void fix_types();

  bool constant_propagation;

protected:
  goto_symex_statet symex_state;
  goto_functionst functions;
  symbol_tablet &symbol_table;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  path_fifot path_storage;
  optionst options;
  goto_symext symex;

  std::unique_ptr<propt> satcheck;
  bv_pointerst satchecker;
  smt2_dect z3;
  prop_convt *checker;
  static optionst get_default_options();
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H
