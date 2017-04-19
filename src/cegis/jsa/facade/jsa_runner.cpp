/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/options.h>

#include <cegis/facade/runner_helper.h>
#include <cegis/options/parameters.h>
#include <cegis/seed/null_seed.h>

#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/genetic/lazy_fitness.h>
#include <cegis/genetic/ga_learn.h>
#include <cegis/genetic/match_select.h>
#include <cegis/genetic/learn_preprocess_seed.h>
#include <cegis/learn/concurrent_learn.h>
#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/value/default_solution.h>
#include <cegis/jsa/genetic/jsa_source_provider.h>
#include <cegis/jsa/genetic/jsa_random.h>
#include <cegis/jsa/genetic/jsa_serialiser.h>
#include <cegis/jsa/genetic/jsa_paragon_wrapper.h>
#include <cegis/jsa/genetic/random_jsa_cross.h>
#include <cegis/jsa/genetic/random_jsa_mutate.h>
#include <cegis/jsa/genetic/jsa_genetic_convert.h>
#include <cegis/jsa/genetic/dynamic_jsa_test_runner.h>
#include <cegis/jsa/preprocessing/jsa_preprocessing.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>
#include <cegis/jsa/verify/jsa_symex_verify.h>
#include <cegis/jsa/facade/jsa_runner.h>

namespace
{
typedef messaget::mstreamt mstreamt;

std::function<void(jsa_solutiont &)> get_default_solution(
    const jsa_programt &prog)
{
  return [&prog](jsa_solutiont &solution)
  { if(solution.invariant.empty()) solution=default_jsa_solution(prog);};
}

template<class oraclet, class prept>
int run_with_ga(const symbol_tablet &st, const optionst &o, mstreamt &result,
    jsa_symex_learnt &l, oraclet &oracle, prept &prep)
{
  jsa_source_providert source_provider(l);
  dynamic_jsa_test_runnert test_runner(std::ref(source_provider));
  typedef lazy_fitnesst<jsa_populationt,
                        dynamic_jsa_test_runnert,
                        jsa_counterexamplet> fitnesst;
  fitnesst fitness(test_runner);
  typedef match_selectt<jsa_populationt> selectt;
  const selectt::test_case_datat &test_case_data=fitness.get_test_case_data();
  const size_t rounds=o.get_unsigned_int_option(CEGIS_ROUNDS);
  const selectt select(test_case_data, rounds);
  jsa_randomt rnd(st, l.get_pred_ops_count(), l.get_const_pred_ops_count());
  const random_jsa_mutatet mutate(rnd);
  const random_jsa_crosst cross(rnd);
  const jsa_genetic_convertt convert(l);
  ga_learnt<const selectt,
            const random_jsa_mutatet,
            const random_jsa_crosst,
            fitnesst,
            const jsa_genetic_convertt> ga(o, rnd, select, mutate, cross, fitness, convert);
  const jsa_serialisert serialiser(l.get_jsa_program());
  const size_t num_sym=o.get_unsigned_int_option(CEGIS_SYMEX_HEAD_START);
  const jsa_paragon_wrappert paragon_wrapper(l);
  typedef cegis_symex_learnt<jsa_preprocessingt, const jsa_paragon_wrappert> symex_learnt;
  symex_learnt symex_learn(o, prep, paragon_wrapper);
  concurrent_learnt<decltype(ga), symex_learnt> learn(ga,
                                                      symex_learn,
                                                      serialiser,
                                                      num_sym);
  learn_preprocess_seedt<jsa_symex_learnt> seed(o, l);
  return run_cegis_with_statistics_wrapper(result, o, learn, oracle, prep, seed);
}
}

int run_jsa(optionst &o, mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf)
{
  jsa_preprocessingt prep(o, st, gf);
  const jsa_programt &prog=prep.get_jsa_program();
  jsa_symex_learnt lcfg(prog);
  cegis_symex_learnt<jsa_preprocessingt, jsa_symex_learnt> learn(o, prep, lcfg, get_default_solution(prog));
  jsa_symex_verifyt vcfg(prog);
  cegis_symex_verifyt<jsa_symex_verifyt> oracle(o, vcfg);
  if(o.get_bool_option(CEGIS_GENETIC))
    return run_with_ga(st, o, result, lcfg, oracle, prep);
  else
    return run_cegis_with_statistics_wrapper(result, o, learn, oracle, prep);
}
