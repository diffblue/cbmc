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
#include "cone_of_influence.h"
#include "acceleration_utils.h"

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
      loop_header(_loop_header),
      utils(symbol_table, goto_functions, loop_counter)
  {
    loop_counter = nil_exprt();
    find_distinguishing_points();
    build_fixed();
    utils.find_modified(loop, modified);
  }

  virtual bool accelerate(path_acceleratort &accelerator);

  bool fit_polynomial(exprt &target,
                      polynomialt &polynomial,
                      patht &path);

  bool find_path(patht &path);

 protected:
  void assert_for_values(scratch_programt &program,
                         map<exprt, exprt> &values,
                         set<pair<expr_listt, exprt> > &coefficients,
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

  typedef map<goto_programt::targett, exprt> distinguish_mapt;
  typedef map<exprt, bool> distinguish_valuest;

  acceleration_utilst utils;
  exprt loop_counter;
  distinguish_mapt distinguishing_points;
  list<exprt> distinguishers;
  expr_sett modified;
  goto_programt fixed;
  list<distinguish_valuest> accelerated_paths;
};

#endif // DISJUNCTIVE_POLYNOMIAL_ACCELERATION_H
