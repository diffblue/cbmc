#ifndef POLYNOMIAL_ACCELERATOR_H
#define POLYNOMIAL_ACCELERATOR_H

#include <map>
#include <set>

#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include "scratch_program.h"
#include "polynomial.h"
#include "path.h"
#include "accelerator.h"
#include "path_acceleration.h"
#include "acceleration_utils.h"
#include "cone_of_influence.h"
#include "overflow_instrumenter.h"

using namespace std;

class polynomial_acceleratort : public path_accelerationt {
 public:
  polynomial_acceleratort(const symbol_tablet &_symbol_table,
                          const goto_functionst &_goto_functions) :
      symbol_table(const_cast<symbol_tablet &>(_symbol_table)),
      ns(symbol_table),
      goto_functions(_goto_functions),
      utils(symbol_table, goto_functions, loop_counter)
  {
    loop_counter = nil_exprt();
  }

  polynomial_acceleratort(const symbol_tablet &_symbol_table,
                          const goto_functionst &_goto_functions,
                          exprt &_loop_counter) :
      symbol_table(const_cast<symbol_tablet &>(_symbol_table)),
      ns(symbol_table),
      goto_functions(_goto_functions),
      utils(symbol_table, goto_functions, loop_counter),
      loop_counter(_loop_counter)
  {
  }

  virtual bool accelerate(patht &loop, path_acceleratort &accelerator);

  bool fit_polynomial(goto_programt::instructionst &loop_body,
                      exprt &target,
                      polynomialt &polynomial);

 protected:
  bool fit_polynomial_sliced(goto_programt::instructionst &sliced_body,
                             exprt &target,
                             expr_sett &influence,
                             polynomialt &polynomial);

  void assert_for_values(scratch_programt &program,
                         map<exprt, int> &values,
                         set<pair<expr_listt, exprt> > &coefficients,
                         int num_unwindings,
                         goto_programt::instructionst &loop_body,
                         exprt &target,
                         overflow_instrumentert &overflow);
  void extract_polynomial(scratch_programt &program,
                          set<pair<expr_listt, exprt> > &coefficients,
                          polynomialt &polynomial);
  void cone_of_influence(goto_programt::instructionst &orig_body,
                         exprt &target,
                         goto_programt::instructionst &body,
                         expr_sett &influence);

  bool fit_const(goto_programt::instructionst &loop_body,
                 exprt &target,
                 polynomialt &polynomial);

  bool check_inductive(map<exprt, polynomialt> polynomials,
                       goto_programt::instructionst &body);
  void stash_variables(scratch_programt &program,
                       expr_sett modified,
                       substitutiont &substitution);
  void stash_polynomials(scratch_programt &program,
                         map<exprt, polynomialt> &polynomials,
                         map<exprt, exprt> &stashed,
                         goto_programt::instructionst &body);

  exprt precondition(patht &path);

  bool do_assumptions(map<exprt, polynomialt> polynomials,
                      patht &body,
                      exprt &guard);

  typedef pair<exprt, exprt> expr_pairt;
  typedef vector<expr_pairt> expr_pairst;

  typedef struct polynomial_array_assignment {
    exprt array;
    polynomialt index;
    polynomialt value;
  } polynomial_array_assignmentt;

  typedef vector<polynomial_array_assignmentt> polynomial_array_assignmentst;

  bool do_arrays(goto_programt::instructionst &loop_body,
                 map<exprt, polynomialt> &polynomials,
                 exprt &loop_counter,
                 substitutiont &substitution,
                 scratch_programt &program);
  expr_pairst gather_array_assignments(goto_programt::instructionst &loop_body,
                                       expr_sett &arrays_written);
  bool array_assignments2polys(expr_pairst &array_assignments,
                               map<exprt, polynomialt> &polynomials,
                               polynomial_array_assignmentst &array_polynomials,
                               polynomialst &nondet_indices);
  bool expr2poly(exprt &expr,
                 map<exprt, polynomialt> &polynomials,
                 polynomialt &poly);

  void ensure_no_overflows(goto_programt &program);


  symbol_tablet &symbol_table;
  const namespacet ns;
  const goto_functionst &goto_functions;
  acceleration_utilst utils;

  exprt loop_counter;

  expr_sett nonrecursive;
};

expr_sett find_modified(goto_programt::instructionst &body);

#endif // POLYNOMIAL_ACCELERATOR_H
