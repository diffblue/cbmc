#ifndef ACCELERATION_UTILS_H
#define ACCELERATION_UTILS_H

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
#include "cone_of_influence.h"

#define DEBUG

using namespace std;

class acceleration_utilst {
 public:
  acceleration_utilst(symbol_tablet &_symbol_table,
                      goto_functionst &_goto_functions,
                      goto_programt &_goto_program,
                      natural_loops_mutablet::natural_loopt &_loop,
                      goto_programt::targett _loop_header,
                      exprt &_loop_counter) :
      symbol_table(_symbol_table),
      ns(symbol_table),
      goto_functions(_goto_functions),
      goto_program(_goto_program),
      loop(_loop),
      loop_header(_loop_header),
      loop_counter(_loop_counter)
  {
  }

  void extract_polynomial(scratch_programt &program,
                          set<pair<expr_listt, exprt> > &coefficients,
                          polynomialt &polynomial);

  bool check_inductive(map<exprt, polynomialt> polynomials,
                       patht &path);
  void stash_variables(scratch_programt &program,
                       expr_sett modified,
                       substitutiont &substitution);
  void stash_polynomials(scratch_programt &program,
                         map<exprt, polynomialt> &polynomials,
                         map<exprt, exprt> &stashed,
                         patht &path);

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

  void gather_rvalues(const exprt &expr, expr_sett &rvalues);

  void ensure_no_overflows(scratch_programt &program);

  void find_modified(patht &path, expr_sett &modified);
  void find_modified(goto_programt &program, expr_sett &modified);
  void find_modified(natural_loops_mutablet::natural_loopt &loop,
      expr_sett &modified);
  void find_modified(goto_programt::targett t, expr_sett &modified);

  symbol_tablet &symbol_table;
  namespacet ns;
  goto_functionst &goto_functions;
  goto_programt &goto_program;
  natural_loops_mutablet::natural_loopt &loop;
  goto_programt::targett loop_header;
  exprt &loop_counter;
};

#endif // ACCELERATION_UTILS_H
