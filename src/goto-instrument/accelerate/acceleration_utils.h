/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_ACCELERATION_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_ACCELERATION_UTILS_H

#include <list>
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

typedef std::unordered_map<exprt, exprt, irep_hash> expr_mapt;
typedef std::list<exprt> expr_listt;

class acceleration_utilst
{
protected:
  message_handlert &message_handler;

public:
  acceleration_utilst(
    symbol_tablet &_symbol_table,
    message_handlert &message_handler,
    const goto_functionst &_goto_functions,
    exprt &_loop_counter)
    : message_handler(message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      loop_counter(_loop_counter)
  {
  }

  acceleration_utilst(
    symbol_tablet &_symbol_table,
    message_handlert &message_handler,
    const goto_functionst &_goto_functions)
    : message_handler(message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      loop_counter(nil)
  {
  }

  void extract_polynomial(scratch_programt &program,
                          std::set<std::pair<expr_listt, exprt> > &coefficients,
                          polynomialt &polynomial);

  bool check_inductive(std::map<exprt, polynomialt> polynomials,
                       patht &path);
  void stash_variables(scratch_programt &program,
                       expr_sett modified,
                       substitutiont &substitution);
  void stash_polynomials(scratch_programt &program,
                         std::map<exprt, polynomialt> &polynomials,
                         std::map<exprt, exprt> &stashed,
                         patht &path);

  exprt precondition(patht &path);
  void abstract_arrays(exprt &expr, expr_mapt &abstractions);
  void push_nondet(exprt &expr);

  bool do_assumptions(std::map<exprt, polynomialt> polynomials,
                      patht &body,
                      exprt &guard);

  typedef std::pair<exprt, exprt> expr_pairt;
  typedef std::vector<expr_pairt> expr_pairst;

  struct polynomial_array_assignmentt
  {
    exprt array;
    polynomialt index;
    polynomialt value;
  };

  typedef std::vector<polynomial_array_assignmentt>
    polynomial_array_assignmentst;

  bool do_arrays(goto_programt::instructionst &loop_body,
                 std::map<exprt, polynomialt> &polynomials,
                 substitutiont &substitution,
                 scratch_programt &program);
  expr_pairst gather_array_assignments(
    goto_programt::instructionst &loop_body,
    expr_sett &arrays_written);
  bool array_assignments2polys(
    expr_pairst &array_assignments,
    std::map<exprt, polynomialt> &polynomials,
    polynomial_array_assignmentst &array_polynomials,
    polynomialst &nondet_indices);
  bool expr2poly(
    exprt &expr,
    std::map<exprt, polynomialt> &polynomials,
    polynomialt &poly);

  bool do_nonrecursive(
    goto_programt::instructionst &loop_body,
    std::map<exprt, polynomialt> &polynomials,
    substitutiont &substitution,
    expr_sett &nonrecursive,
    scratch_programt &program);
  bool assign_array(
    const exprt &lhs,
    const exprt &rhs,
    scratch_programt &program);

  void gather_array_accesses(const exprt &expr, expr_sett &arrays);

  void gather_rvalues(const exprt &expr, expr_sett &rvalues);

  void ensure_no_overflows(scratch_programt &program);

  void find_modified(const patht &path, expr_sett &modified);
  void find_modified(
    const goto_programt &program,
    expr_sett &modified);
  void find_modified(
    const goto_programt::instructionst &instructions,
    expr_sett &modified);
  void find_modified(
    const natural_loops_mutablet::natural_loopt &loop,
    expr_sett &modified);
  void find_modified(
    goto_programt::const_targett t,
    expr_sett &modified);

  symbolt fresh_symbol(std::string base, typet type);

  symbol_tablet &symbol_table;
  namespacet ns;
  const goto_functionst &goto_functions;
  exprt &loop_counter;
  nil_exprt nil;

  static int num_symbols;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_ACCELERATION_UTILS_H
