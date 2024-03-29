/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H

#include <memory>

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

// Wrapper around goto_symext to make initialize_entry_point_state available.
struct scratch_program_symext : public goto_symext
{
  scratch_program_symext(
    message_handlert &mh,
    const symbol_table_baset &outer_symbol_table,
    symex_target_equationt &_target,
    const optionst &options,
    path_storaget &path_storage,
    guard_managert &guard_manager)
    : goto_symext(
        mh,
        outer_symbol_table,
        _target,
        options,
        path_storage,
        guard_manager)
  {
  }

  std::unique_ptr<statet>
  initialize_entry_point_state(const get_goto_functiont &get_goto_function)
  {
    return goto_symext::initialize_entry_point_state(get_goto_function);
  }
};

class scratch_programt:public goto_programt
{
public:
  scratch_programt(
    symbol_table_baset &_symbol_table,
    message_handlert &mh,
    guard_managert &guard_manager)
    : constant_propagation(true),
      symbol_table(_symbol_table),
      symex_symbol_table(),
      ns(symbol_table, symex_symbol_table),
      equation(mh),
      path_storage(),
      options(get_default_options()),
      symex(mh, symbol_table, equation, options, path_storage, guard_manager),
      satcheck(std::make_unique<satcheckt>(mh)),
      satchecker(ns, *satcheck, mh),
      z3(ns, "accelerate", "", "", smt2_dect::solvert::Z3, mh),
      checker(&z3) // checker(&satchecker)
  {
  }

  void append(goto_programt::instructionst &instructions);
  void append(goto_programt &program);
  void append_path(patht &path);
  void append_loop(goto_programt &program, goto_programt::targett loop_header);

  targett assign(const exprt &lhs, const exprt &rhs);
  targett assume(const exprt &guard);

  bool check_sat(bool do_slice, guard_managert &guard_manager);

  bool check_sat(guard_managert &guard_manager)
  {
    return check_sat(true, guard_manager);
  }

  exprt eval(const exprt &e);

  void fix_types();

  bool constant_propagation;

protected:
  std::unique_ptr<goto_symex_statet> symex_state;
  goto_functionst functions;
  symbol_table_baset &symbol_table;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  path_fifot path_storage;
  optionst options;
  scratch_program_symext symex;

  std::unique_ptr<propt> satcheck;
  bv_pointerst satchecker;
  smt2_dect z3;
  decision_proceduret *checker;
  static optionst get_default_options();
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_SCRATCH_PROGRAM_H
