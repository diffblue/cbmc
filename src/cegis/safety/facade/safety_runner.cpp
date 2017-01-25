/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstdlib>

#include <util/options.h>

#include <cegis/danger/meta/literals.h>

#include <cegis/facade/cegis.h>
#include <cegis/options/parameters.h>
#include <cegis/statistics/cegis_statistics_wrapper.h>
#include <cegis/genetic/genetic_preprocessing.h>
#include <cegis/genetic/genetic_constant_strategy.h>
#include <cegis/genetic/lazy_genetic_settings.h>
#include <cegis/genetic/instruction_set_info_factory.h>
#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/random_mutate.h>
#include <cegis/genetic/random_cross.h>
#include <cegis/genetic/match_select.h>
#include <cegis/genetic/lazy_fitness.h>
#include <cegis/genetic/ga_learn.h>
#include <cegis/genetic/tournament_select.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/seed/null_seed.h>
#include <cegis/learn/concurrent_learn.h>
#include <cegis/value/program_individual_serialisation.h>
#include <cegis/invariant/constant/constant_strategy.h>
#include <cegis/invariant/constant/default_constant_strategy.h>
#include <cegis/invariant/fitness/concrete_fitness_source_provider.h>
#include <cegis/invariant/symex/learn/invariant_body_provider.h>
#include <cegis/safety/value/safety_goto_ce.h>
#include <cegis/safety/value/individual_to_safety_solution_deserialiser.h>
#include <cegis/safety/options/safety_program_genetic_settings.h>
#include <cegis/safety/preprocessing/safety_preprocessing.h>
#include <cegis/safety/genetic/dynamic_safety_test_runner.h>
#include <cegis/safety/symex/fitness/safety_fitness_config.h>
#include <cegis/safety/symex/learn/safety_learn_config.h>
#include <cegis/safety/symex/learn/encoded_safety_learn_config.h>
#include <cegis/safety/symex/verify/safety_verify_config.h>
#include <cegis/safety/facade/safety_runner.h>

namespace
{
typedef messaget::mstreamt mstreamt;

template<class learnt, class verifyt, class preproct>
int configure_ui_and_run(mstreamt &os, const optionst &opt, learnt &learn,
    verifyt &verify, preproct &preproc)
{
  null_seedt seed;
  const size_t max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  if (!opt.get_bool_option(CEGIS_STATISTICS))
    return run_cegis(learn, verify, preproc, seed, max_prog_size, os);
  cegis_statistics_wrappert<learnt, verifyt, mstreamt> stat(learn, verify, os, opt);
  return run_cegis(stat, stat, preproc, seed, max_prog_size, os);
}

template<class learnt, class verifyt, class prept>
int configure_backend(mstreamt &os, const optionst &o,
    const safety_programt &prog, learnt &cfg, verifyt &verify, prept &prep)
{
  if (!o.get_bool_option(CEGIS_GENETIC))
  {
    cegis_symex_learnt<safety_preprocessingt, learnt> learn(o, prep, cfg);
    return configure_ui_and_run(os, o, learn, verify, prep);
  }
  encoded_safety_learn_configt enc(cfg);
  typedef genetic_preprocessingt<prept> preproct;
  preproct pre(o, prep);
  typedef cegis_symex_learnt<preproct, encoded_safety_learn_configt> symex_learnt;
  symex_learnt learn(o, pre, enc);
  safety_program_genetic_settingst<preproct> set(o, prog, pre);
  lazy_genetic_settingst<safety_program_genetic_settingst<preproct> > lazy(set);
  invariant_exec_body_providert<safety_programt> body(DANGER_EXECUTE, prog);
  instruction_set_info_factoryt info_fac(std::ref(body));
  const size_t rounds=o.get_unsigned_int_option(CEGIS_ROUNDS);
  const typet type=cegis_default_integer_type(); // XXX: Currently single user data type.
  random_individualt rnd(type, info_fac, lazy);
  safety_fitness_configt safety_fitness_config(info_fac, prog);
  concrete_fitness_source_providert<safety_programt, safety_learn_configt> src(
      prog, lazy.max_prog_sz_provider(), DANGER_EXECUTE);
  dynamic_safety_test_runnert test_runner(std::ref(src),
      lazy.max_prog_sz_per_index_provider());
  typedef lazy_fitnesst<program_populationt, dynamic_safety_test_runnert,
      safety_goto_cet> fitnesst;
  fitnesst fit(test_runner);
  random_mutatet mutate(rnd, lazy.num_consts_provder());
  random_crosst cross(rnd);
  const size_t symex_head_start=o.get_unsigned_int_option(CEGIS_SYMEX_HEAD_START);
  if (o.get_bool_option(CEGIS_MATCH_SELECT))
  {
    typedef match_selectt<program_populationt> selectt;
    selectt select(fit.get_test_case_data(), rnd, rounds);
    typedef ga_learnt<selectt, random_mutatet, random_crosst,
        lazy_fitnesst<program_populationt, dynamic_safety_test_runnert,
            safety_goto_cet>, safety_fitness_configt> ga_learnt;
    ga_learnt ga_learn(o, rnd, select, mutate, cross, fit, safety_fitness_config);
#ifndef _WIN32
    if (!o.get_bool_option(CEGIS_GENETIC_ONLY))
    {
      const individual_to_safety_solution_deserialisert deser(prog, info_fac);
      concurrent_learnt<ga_learnt, symex_learnt> learner(ga_learn, learn,
          serialise, deser, deserialise, symex_head_start);
      return configure_ui_and_run(os, o, learner, verify, pre);
    }
#endif
    return configure_ui_and_run(os, o, ga_learn, verify, pre);
  }
  typedef tournament_selectt<program_populationt> selectt;
  selectt select(rounds);
  typedef ga_learnt<selectt, random_mutatet, random_crosst,
      lazy_fitnesst<program_populationt, dynamic_safety_test_runnert,
          safety_goto_cet>, safety_fitness_configt> ga_learnt;
  ga_learnt ga_learn(o, rnd, select, mutate, cross, fit, safety_fitness_config);
#ifndef _WIN32
  if (!o.get_bool_option(CEGIS_GENETIC_ONLY))
  {
    const individual_to_safety_solution_deserialisert deser(prog, info_fac);
    concurrent_learnt<ga_learnt, symex_learnt> learner(ga_learn, learn,
        serialise, std::ref(deser), deserialise, symex_head_start);
    return configure_ui_and_run(os, o, learner, verify, pre);
  }
#endif
  return configure_ui_and_run(os, o, ga_learn, verify, pre);
}

constant_strategyt get_constant_strategy(const optionst &opt)
{
  if (opt.get_bool_option(CEGIS_GENETIC)) return genetic_constant_strategy;
  return default_constant_strategy;
}
}

int run_safety(optionst &options, mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf)
{
  srand(options.get_unsigned_int_option(CEGIS_SEED));
  safety_preprocessingt prep(options, st, gf, get_constant_strategy(options));
  const safety_programt &safety_program=prep.get_safety_program();
  safety_learn_configt learn(safety_program);
  safety_verify_configt verify_cfg(safety_program);
  cegis_symex_verifyt<safety_verify_configt> verify(options, verify_cfg);
  return configure_backend(result, options, safety_program, learn, verify, prep);
}
