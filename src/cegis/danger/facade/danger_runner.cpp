#include <cstdlib>

#include <util/cmdline.h>
#include <util/message.h>

#include <cegis/facade/cegis.h>
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
#include <cegis/genetic/concrete_test_runner.h>
#include <cegis/genetic/dynamic_test_runner.h>
#include <cegis/seed/null_seed.h>
#include <cegis/seed/literals_seed.h>
#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/learn/concurrent_learn.h>
#include <cegis/statistics/cegis_statistics_wrapper.h>
#include <cegis/value/program_individual_serialisation.h>
#include <cegis/wordsize/limited_wordsize_verify.h>

#include <cegis/danger/constant/constant_strategy.h>
#include <cegis/danger/constant/default_constant_strategy.h>
#include <cegis/danger/fitness/concrete_fitness_source_provider.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/preprocess/danger_preprocessing.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/danger_learn_config.h>
#include <cegis/danger/symex/learn/encoded_danger_learn_config.h>
#include <cegis/danger/symex/learn/danger_body_provider.h>
#include <cegis/danger/symex/verify/danger_verify_config.h>
#include <cegis/danger/symex/verify/parallel_danger_verifier.h>
#include <cegis/danger/symex/fitness/danger_fitness_config.h>
#include <cegis/danger/facade/danger_runner.h>

namespace
{
bool is_genetic(const optionst &opt)
{
  return opt.get_bool_option("cegis-genetic");
}

#define DANGER_MAX_SIZE "cegis-max-size"
#define DANGER_STATISTICS "cegis-statistics"

typedef messaget::mstreamt mstreamt;

template<class learnt, class verifyt, class preproct>
int run_statistics(mstreamt &os, const optionst &options,
    const danger_programt &prog, learnt &learn, verifyt &verify,
    preproct &preproc)
{
  null_seedt seed;
  //danger_literals_seedt seed(prog);  // XXX: Benchmark performance
  const size_t max_prog_size=options.get_unsigned_int_option(DANGER_MAX_SIZE);
  if (!options.get_bool_option(DANGER_STATISTICS))
    return run_cegis(learn, verify, preproc, seed, max_prog_size, os);
  cegis_statistics_wrappert<learnt, verifyt, mstreamt> stat(learn, verify, os);
  return run_cegis(stat, stat, preproc, seed, max_prog_size, os);
}

#define CEGIS_LIMIT_WORDSIZE "cegis-limit-wordsize"

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

#define DANGER_PARALLEL_VERIFY "cegis-parallel-verify"

template<class learnert, class preproct>
int run_parallel(mstreamt &os, optionst &options, const danger_programt &prog,
    learnert &learn, preproct &preproc)
{
  danger_verify_configt config(prog);
  if (options.get_bool_option(DANGER_PARALLEL_VERIFY))
  {
    parallel_danger_verifiert verify(options, config);
    return run_limited(os, options, prog, config, learn, verify, preproc);
  }
  cegis_symex_verifyt<danger_verify_configt> verify(options, config);
  return run_limited(os, options, prog, config, learn, verify, preproc);
}

class variable_counter_helper
{
  const danger_programt &prog;
  bool counted;
  size_t num_vars;
  size_t num_consts;

  const size_t &count(size_t &value)
  {
    if (!counted)
    {
      danger_variable_idst ids;
      num_consts=get_danger_variable_ids(prog.st, ids);
      num_vars=ids.size();
      counted=true;
    }
    return value;
  }
public:
  variable_counter_helper(const danger_programt &prog) :
      prog(prog), counted(false), num_vars(0), num_consts(0)
  {
  }

  size_t get_num_vars()
  {
    return count(num_vars);
  }

  size_t get_num_consts()
  {
    return count(num_consts);
  }
};

class lazy_sizet
{
  const std::function<size_t(void)> func;
  size_t size;
  bool initialised;
public:
  lazy_sizet(const std::function<size_t(void)> &func) :
      func(func), size(0), initialised(false)
  {
  }

  size_t operator()()
  {
    if (initialised) return size;
    initialised=true;
    return size=func();
  }
};

#define SKOLEM_PROG_INDEX 2u

class min_danger_prog_sizet
{
  lazy_sizet &preproc_min_prog_size;
  const size_t user_min_prog_size;
public:
  min_danger_prog_sizet(lazy_sizet &preproc_min_prog_size, const optionst &opt) :
      preproc_min_prog_size(preproc_min_prog_size), user_min_prog_size(
          opt.get_unsigned_int_option("cegis-min-size"))
  {
  }

  size_t operator()(const size_t prog_index) const
  {
    if (SKOLEM_PROG_INDEX == prog_index)
      return std::max(user_min_prog_size, preproc_min_prog_size());
    return user_min_prog_size;
  }
};

const size_t PROGS_PER_LOOP=3u;

class max_danger_prog_sizet
{
  const danger_programt &prog;
  const size_t user_max_prog_size;
public:
  max_danger_prog_sizet(const danger_programt &prog, const optionst &opt) :
      prog(prog), user_max_prog_size(
          opt.get_unsigned_int_option("cegis-max-size"))
  {
  }

  size_t operator()(const size_t prog_index) const
  {
    if (SKOLEM_PROG_INDEX == prog_index % PROGS_PER_LOOP)
    {
      const size_t loop_index=prog_index / PROGS_PER_LOOP;
      const size_t num_skolem=prog.loops[loop_index].skolem_choices.size();
      if (num_skolem == 0u) return 0u;
      return std::max(num_skolem, user_max_prog_size);
    }
    return user_max_prog_size;
  }

  size_t operator()() const
  {
    const danger_programt::loopst &l=prog.loops;
    const size_t max_num_skolem=
        std::max_element(l.begin(), l.end(),
            [](const danger_programt::loopt &l, const danger_programt::loopt &r)
            { return l.skolem_choices.size() < r.skolem_choices.size();})->skolem_choices.size();
    return std::max(max_num_skolem, user_max_prog_size);
  }
};

#define CEGIS_MATCH_SELECT "cegis-match-select"

template<class fitnesst, class mutatet, class crosst, class convertert,
    class preproct, class symex_learnt>
int run_match(mstreamt &os, optionst &opt, const danger_programt &prog,
    random_individualt &rnd, instruction_set_info_factoryt &info_fac,
    const size_t pop_size, const size_t rounds, fitnesst &fitness,
    mutatet &mutate, crosst &cross, convertert &converter, preproct &preproc,
    symex_learnt &symex_learn)
{
  const individual_to_danger_solution_deserialisert deser(prog, info_fac);
  if (opt.get_bool_option(CEGIS_MATCH_SELECT))
  {
    match_selectt select(fitness.get_test_case_data(), rnd, pop_size, rounds);
    typedef ga_learnt<match_selectt, mutatet, crosst, fitnesst,
        danger_fitness_configt> ga_learnt;
    ga_learnt ga_learn(opt, select, mutate, cross, fitness, converter);
#ifndef _WIN32
    concurrent_learnt<ga_learnt, symex_learnt> learn(ga_learn, symex_learn,
        serialise, std::ref(deser), deserialise);
#else
    // TODO: Remove once task_pool supports Windows.
    ga_learnt &learn=ga_learn;
#endif
    return run_parallel(os, opt, prog, learn, preproc);
  }
  tournament_selectt select(rnd, pop_size, rounds);
  typedef ga_learnt<tournament_selectt, random_mutatet, random_crosst, fitnesst,
      danger_fitness_configt> ga_learnt;
  ga_learnt ga_learn(opt, select, mutate, cross, fitness, converter);
#ifndef _WIN32
  concurrent_learnt<ga_learnt, symex_learnt> learn(ga_learn, symex_learn,
      serialise, std::ref(deser), deserialise);
#else
  // TODO: Remove once task_pool supports Windows.
  ga_learnt &learn=ga_learn;
#endif
  return run_parallel(os, opt, prog, learn, preproc);

}

template<class preproct>
int run_genetic_and_symex(mstreamt &os, optionst &opt,
    const danger_programt &prog, preproct &preproc)
{
  if (!is_genetic(opt))
  {
    danger_learn_configt cfg(prog);
    cegis_symex_learnt<preproct, danger_learn_configt> learn(opt, preproc, cfg);
    return run_parallel(os, opt, prog, learn, preproc);
  }
  typedef encoded_danger_learn_configt cfgt;
  cfgt cfg(prog);
  cegis_symex_learnt<preproct, cfgt> learn(opt, preproc, cfg);

  // Danger program properties and GA settings
  const unsigned int seed=opt.get_unsigned_int_option("cegis-seed");
  danger_body_providert body(prog);
  instruction_set_info_factoryt info_fac(std::ref(body));
  const size_t pop_size=opt.get_unsigned_int_option("cegis-genetic-popsize");
  const lazy_sizet num_progs([&prog]()
  { return prog.loops.size() * 3u;});
  lazy_sizet num_x0([&prog]()
  { return prog.x0_choices.size();});
  lazy_sizet preproc_min_size([&preproc]()
  { return preproc.get_min_solution_size();});
  const min_danger_prog_sizet min_prog_sz(preproc_min_size, opt);
  const max_danger_prog_sizet max_prog_sz(prog, opt);
  const size_t rounds=opt.get_unsigned_int_option("cegis-genetic-rounds");
  variable_counter_helper counter(prog);
  const lazy_sizet num_vars([&counter]()
  { return counter.get_num_vars();});
  const lazy_sizet num_consts([&counter]()
  { return counter.get_num_consts();});

  // Set-up genetic algorithm
  const typet type=danger_meta_type(); // XXX: Currently single user data type.
  random_individualt rnd(seed, type, info_fac, min_prog_sz, max_prog_sz,
      num_progs, num_vars, num_consts, num_x0);
  danger_fitness_configt converter(info_fac, prog);
  concrete_fitness_source_providert src(prog, std::ref(max_prog_sz));
  dynamic_test_runnert test_runner(std::ref(src), std::ref(max_prog_sz));
  typedef lazy_fitnesst<dynamic_test_runnert> fitnesst;
  fitnesst fitness(test_runner);
  random_mutatet mutate(rnd, num_consts);
  random_crosst cross(rnd);
  return run_match(os, opt, prog, rnd, info_fac, pop_size, rounds, fitness,
      mutate, cross, converter, preproc, learn);
}
}

int run_danger(optionst &options, mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf)
{
  srand(options.get_unsigned_int_option("cegis-seed"));
  const bool is_gen=is_genetic(options);
  const constant_strategyt str=
      is_gen ? genetic_constant_strategy : default_constant_strategy;
  danger_preprocessingt preproc(options, st, gf, str);
  const danger_programt &prog=preproc.get_danger_program();
  genetic_preprocessingt<danger_preprocessingt> gen_preproc(options, preproc);
  return run_genetic_and_symex(result, options, prog, gen_preproc);
}
