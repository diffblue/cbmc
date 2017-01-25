/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstdlib>

#include <util/cmdline.h>
#include <util/message.h>

#include <cegis/facade/cegis.h>
#include <cegis/genetic/lazy_genetic_settings.h>
#include <cegis/genetic/ga_learn.h>
#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/match_select.h>
#include <cegis/genetic/tournament_select.h>
#include <cegis/genetic/instruction_set_info_factory.h>
#include <cegis/genetic/random_mutate.h>
#include <cegis/genetic/random_cross.h>
#include <cegis/genetic/genetic_constant_strategy.h>
#include <cegis/genetic/genetic_preprocessing.h>
#include <cegis/genetic/lazy_fitness.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/seed/null_seed.h>
#include <cegis/seed/literals_seed.h>
#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/learn/concurrent_learn.h>
#include <cegis/statistics/cegis_statistics_wrapper.h>
#include <cegis/value/program_individual_serialisation.h>
#include <cegis/wordsize/limited_wordsize_verify.h>

#include <cegis/invariant/fitness/concrete_fitness_source_provider.h>
#include <cegis/invariant/constant/constant_strategy.h>
#include <cegis/invariant/constant/default_constant_strategy.h>
#include <cegis/invariant/symex/learn/invariant_body_provider.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program_genetic_settings.h>
#include <cegis/danger/preprocess/danger_preprocessing.h>
#include <cegis/danger/genetic/dynamic_danger_test_runner.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/danger_learn_config.h>
#include <cegis/danger/symex/learn/encoded_danger_learn_config.h>
#include <cegis/danger/symex/verify/danger_verify_config.h>
#include <cegis/danger/symex/verify/parallel_danger_verifier.h>
#include <cegis/danger/symex/fitness/danger_fitness_config.h>
#include <cegis/danger/facade/danger_runner.h>

namespace
{
bool is_genetic(const optionst &opt)
{
  return opt.get_bool_option(CEGIS_GENETIC);
}

typedef messaget::mstreamt mstreamt;

template<class learnt, class verifyt, class preproct>
int run_statistics(mstreamt &os, const optionst &opt,
    const danger_programt &prog, learnt &learn, verifyt &verify,
    preproct &preproc)
{
  null_seedt seed;
  //danger_literals_seedt seed(prog);  // XXX: Benchmark performance
  const size_t max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  if (!opt.get_bool_option(CEGIS_STATISTICS))
    return run_cegis(learn, verify, preproc, seed, max_prog_size, os);
  cegis_statistics_wrappert<learnt, verifyt, mstreamt> stat(learn, verify, os, opt);
  return run_cegis(stat, stat, preproc, seed, max_prog_size, os);
}

template<class learnert, class verifiert, class preproct>
int run_limited(mstreamt &os, optionst &options, const danger_programt &prog,
    danger_verify_configt &config, learnert &learn, verifiert &verify,
    preproct &preproc)
{
  if (!options.get_bool_option(CEGIS_LIMIT_WORDSIZE))
    return run_statistics(os, options, prog, learn, verify, preproc);
  limited_wordsize_verifyt<verifiert> limited_verify(options, verify,
      [&config](const size_t width)
      { config.set_max_ce_width(width);});
  return run_statistics(os, options, prog, learn, limited_verify, preproc);
}

template<class learnert, class preproct>
int run_parallel(mstreamt &os, optionst &options, const danger_programt &prog,
    learnert &learn, preproct &preproc)
{
  danger_verify_configt config(prog);
  if (options.get_bool_option(CEGIS_PARALLEL_VERIFY))
  {
    parallel_danger_verifiert verify(options, config);
    return run_limited(os, options, prog, config, learn, verify, preproc);
  }
  cegis_symex_verifyt<danger_verify_configt> verify(options, config);
  return run_limited(os, options, prog, config, learn, verify, preproc);
}

template<class fitnesst, class mutatet, class crosst, class convertert,
    class preproct, class symex_learnt>
int run_match(mstreamt &os, optionst &opt, const danger_programt &prog,
    random_individualt &rnd, instruction_set_info_factoryt &info_fac,
    const size_t rounds, fitnesst &fitness, mutatet &mutate, crosst &cross,
    convertert &converter, preproct &preproc, symex_learnt &symex_learn)
{
  const size_t symex_head_start=opt.get_unsigned_int_option(CEGIS_SYMEX_HEAD_START);
  const individual_to_danger_solution_deserialisert deser(prog, info_fac);
  if (opt.get_bool_option(CEGIS_MATCH_SELECT))
  {
    typedef match_selectt<program_populationt> selectt;
    selectt select(fitness.get_test_case_data(), rnd, rounds);
    typedef ga_learnt<selectt, mutatet, crosst, fitnesst, danger_fitness_configt> ga_learnt;
    ga_learnt ga_learn(opt, rnd, select, mutate, cross, fitness, converter);
#ifndef _WIN32
    if (!opt.get_bool_option(CEGIS_GENETIC_ONLY))
    {
      concurrent_learnt<ga_learnt, symex_learnt> learn(ga_learn, symex_learn,
          serialise, std::ref(deser), deserialise, symex_head_start);
      return run_parallel(os, opt, prog, learn, preproc);
    }
#endif
    return run_parallel(os, opt, prog, ga_learn, preproc);
  }
  typedef tournament_selectt<program_populationt> selectt;
  selectt select(rounds);
  typedef ga_learnt<selectt, mutatet, crosst, fitnesst, danger_fitness_configt> ga_learnt;
  ga_learnt ga_learn(opt, rnd, select, mutate, cross, fitness, converter);
#ifndef _WIN32
  if (!opt.get_bool_option(CEGIS_GENETIC_ONLY))
  {
    concurrent_learnt<ga_learnt, symex_learnt> learn(ga_learn, symex_learn,
        serialise, std::ref(deser), deserialise, symex_head_start);
    return run_parallel(os, opt, prog, learn, preproc);
  }
#endif
  return run_parallel(os, opt, prog, ga_learn, preproc);
}

template<class preproct>
int run_genetic_and_symex(mstreamt &os, optionst &opt,
    const danger_programt &prog, preproct &prep)
{
  if (!is_genetic(opt))
  {
    danger_learn_configt cfg(prog);
    cegis_symex_learnt<preproct, danger_learn_configt> learn(opt, prep, cfg);
    return run_parallel(os, opt, prog, learn, prep);
  }
  typedef encoded_danger_learn_configt cfgt;
  cfgt cfg(prog);
  cegis_symex_learnt<preproct, cfgt> learn(opt, prep, cfg);

  // Danger program properties and GA settings
  danger_program_genetic_settingst<preproct> set(opt, prog, prep);
  lazy_genetic_settingst<danger_program_genetic_settingst<preproct> > lazy(set);
  invariant_exec_body_providert<danger_programt> body(DANGER_EXECUTE, prog);
  instruction_set_info_factoryt info_fac(std::ref(body));
  const size_t rounds=opt.get_unsigned_int_option(CEGIS_ROUNDS);

  // Set-up genetic algorithm
  const typet type=cegis_default_integer_type(); // XXX: Currently single user data type.
  random_individualt rnd(type, info_fac, lazy);
  danger_fitness_configt converter(info_fac, prog);
  concrete_fitness_source_providert<danger_programt, danger_learn_configt> src(
      prog, lazy.max_prog_sz_provider(), DANGER_EXECUTE);
  dynamic_danger_test_runnert test_runner(std::ref(src),
      lazy.max_prog_sz_per_index_provider());
  typedef lazy_fitnesst<program_populationt, dynamic_danger_test_runnert,
      danger_learn_configt::counterexamplet> fitnesst;
  fitnesst fitness(test_runner);
  random_mutatet mutate(rnd, lazy.num_consts_provder());
  random_crosst cross(rnd);
  return run_match(os, opt, prog, rnd, info_fac, rounds, fitness, mutate, cross,
      converter, prep, learn);
}
}

int run_danger(optionst &options, mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf)
{
  srand(options.get_unsigned_int_option(CEGIS_SEED));
  const bool is_gen=is_genetic(options);
  const constant_strategyt str=
      is_gen ? genetic_constant_strategy : default_constant_strategy;
  danger_preprocessingt preproc(options, st, gf, str);
  const danger_programt &prog=preproc.get_danger_program();
  genetic_preprocessingt<danger_preprocessingt> gen_preproc(options, preproc);
  return run_genetic_and_symex(result, options, prog, gen_preproc);
}
