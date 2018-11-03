/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H

#include <map>
#include <set>

#include <util/symbol_table.h>
#include <util/message.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <analyses/natural_loops.h>

#include "scratch_program.h"
#include "polynomial.h"
#include "path.h"
#include "accelerator.h"
#include "cone_of_influence.h"
#include "acceleration_utils.h"

class disjunctive_polynomial_accelerationt
{
public:
  disjunctive_polynomial_accelerationt(
    message_handlert &message_handler,
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    goto_programt &_goto_program,
    natural_loops_mutablet::natural_loopt &_loop,
    goto_programt::targett _loop_header)
    : message_handler(message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      goto_program(_goto_program),
      loop(_loop),
      loop_header(_loop_header),
      utils(symbol_table, message_handler, goto_functions, loop_counter)
  {
    loop_counter = nil_exprt();
    find_distinguishing_points();
    build_fixed();
    utils.find_modified(loop, modified);
  }

  bool accelerate(path_acceleratort &accelerator);

  bool fit_polynomial(
    exprt &target,
    polynomialt &polynomial,
    patht &path);

  bool find_path(patht &path);

protected:
  message_handlert &message_handler;

  void assert_for_values(
    scratch_programt &program,
    std::map<exprt, exprt> &values,
    std::set<std::pair<expr_listt, exprt> > &coefficients,
    int num_unwindings,
    goto_programt &loop_body,
    exprt &target);
  void cone_of_influence(const exprt &target, expr_sett &cone);

  void find_distinguishing_points();

  void build_path(scratch_programt &scratch_program, patht &path);
  void build_fixed();

  void record_path(scratch_programt &scratch_program);

  bool depends_on_array(const exprt &e, exprt &array);

  symbol_tablet &symbol_table;
  namespacet ns;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;

  typedef std::map<goto_programt::targett, exprt> distinguish_mapt;
  typedef std::map<exprt, bool> distinguish_valuest;

  acceleration_utilst utils;
  exprt loop_counter;
  distinguish_mapt distinguishing_points;
  std::list<symbol_exprt> distinguishers;
  expr_sett modified;
  goto_programt fixed;
  std::list<distinguish_valuest> accelerated_paths;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H
