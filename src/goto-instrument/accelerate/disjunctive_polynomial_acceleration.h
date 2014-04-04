#ifndef DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H
#define DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H

#include <map>
#include <set>

#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <analyses/natural_loops.h>

#include "scratch_program.h"
#include "polynomial.h"
#include "path.h"
#include "accelerator.h"
#include "loop_acceleration.h"

using namespace std;

class disjunctive_polynomial_accelerationt : public loop_accelerationt {
 public:
  disjunctive_polynomial_accelerationt(symbol_tablet &_symbol_table,
                          goto_functionst &_goto_functions,
                          goto_programt &_goto_program,
                          natural_loops_mutablet::natural_loopt &_loop,
                          goto_programt::targett _loop_header) :
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      goto_program(_goto_program),
      loop(_loop),
      loop_header(_loop_header)
  {
    loop_counter = nil_exprt();
  }

  virtual bool accelerate(path_acceleratort &accelerator);

  bool fit_polynomial(goto_programt::instructionst &loop_body,
                      exprt &target,
                      polynomialt &polynomial);

 protected:
  void assert_for_values(scratch_programt &program,
                         map<exprt, int> &values,
                         set<pair<expr_listt, exprt> > &coefficients,
                         int num_unwindings,
                         goto_programt::instructionst &loop_body,
                         exprt &target);
  void extract_polynomial(scratch_programt &program,
                          set<pair<expr_listt, exprt> > &coefficients,
                          polynomialt &polynomial);
  set<exprt> cone_of_influence(goto_programt::instructionst &body, exprt &target);

  bool check_inductive(map<exprt, polynomialt> polynomials,
                       goto_programt::instructionst &body);
  void stash_variables(scratch_programt &program,
                       set<exprt> modified,
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
                                       set<exprt> &arrays_written);
  bool array_assignments2polys(expr_pairst &array_assignments,
                               map<exprt, polynomialt> &polynomials,
                               polynomial_array_assignmentst &array_polynomials,
                               polynomialst &nondet_indices);
  bool expr2poly(exprt &expr,
                 map<exprt, polynomialt> &polynomials,
                 polynomialt &poly);

  void ensure_no_overflows(goto_programt &program);


  symbol_tablet &symbol_table;
  namespacet ns;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;

  exprt loop_counter;
};

set<exprt> find_modified(goto_programt::instructionst &body);

#endif // DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H
