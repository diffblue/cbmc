/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/facade/runner_helper.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/value/control_vector_solution.h>
#include <cegis/control/preprocessing/control_preprocessing.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/control_symex_learn.h>
#include <cegis/control/learn/rational_solution_configuration.h>
#include <cegis/control/learn/vector_solution_configuration.h>
#include <cegis/control/verify/control_symex_verify.h>
#include <cegis/control/verify/zero_solutions.h>
#include <cegis/control/facade/control_runner.h>

namespace
{
template<class solution_configt, class zero_solutiont>
int run(optionst &o, messaget::mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf, const zero_solutiont &default_solution)
{
  control_preprocessingt prep(st, gf);
  const control_programt &program=prep.get_program();
  typedef control_symex_learnt<solution_configt> control_learnt;
  control_learnt lcfg(program);
  cegis_symex_learnt<control_preprocessingt, control_learnt> learn(o, prep,
      lcfg, default_solution);
  typedef control_symex_verifyt<typename solution_configt::solutiont> verifyt;
  verifyt vcfg(program);
  cegis_symex_verifyt<verifyt> oracle(o, vcfg);
  return run_cegis_with_statistics_wrapper(result, o, learn, oracle, prep);
}
}

int run_control(optionst &o, messaget::mstreamt &result,
    const symbol_tablet &st, const goto_functionst &gf)
{
  if (is_vector_solution_config(st))
  {
    const zero_vector_solutiont def(st);
    return run<vector_solution_configurationt>(o, result, st, gf, def);
  }
  const zero_rational_solutiont def(st);
  return run<rational_solution_configurationt>(o, result, st, gf, def);
}
