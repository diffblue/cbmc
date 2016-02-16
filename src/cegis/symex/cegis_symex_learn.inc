#include <goto-programs/safety_checker.h>

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>

#include <cegis/cegis-util/constant_width.h>

#define CONSTANT_WIDTH_OPTION "max-constant-width"
#define CEGIS_DEFAULT_MIN_WORD_WIDTH 4u

template<class preproct, class learn_configurationt>
cegis_symex_learnt<preproct, learn_configurationt>::cegis_symex_learnt(
    const optionst &options, preproct &preproc, learn_configurationt &config) :
    options(options), preproc(preproc), config(config), word_width(
    CEGIS_DEFAULT_MIN_WORD_WIDTH), current_solution_size(1u), max_solution_size(
        current_solution_size)
{
}

template<class preproct, class learn_configurationt>
cegis_symex_learnt<preproct, learn_configurationt>::~cegis_symex_learnt()
{
}

template<class preproct, class learn_configurationt>
template<class seedt>
void cegis_symex_learnt<preproct, learn_configurationt>::seed(seedt &seed)
{
  seed(counterexamples);
}

template<class preproct, class learn_configurationt>
const typename cegis_symex_learnt<preproct, learn_configurationt>::candidatet &cegis_symex_learnt<
    preproct, learn_configurationt>::next_candidate() const
{
  return current_candidate;
}

namespace
{
safety_checkert::resultt cegis_learn_run_bmc(goto_tracet &trace,
    const symbol_tablet &st, const goto_functionst &gf, message_handlert &msg,
    const optionst &opt)
{
  cbmc_solverst solvers(opt, st, msg);
  const std::unique_ptr<cbmc_solverst::solvert> solver=solvers.get_solver();
  bmct bmc(opt, st, msg, solver->prop_conv());

  const safety_checkert::resultt bmc_result=bmc(gf);
  if (safety_checkert::UNSAFE != bmc_result) return bmc_result;
  trace=bmc.safety_checkert::error_trace;
  return safety_checkert::UNSAFE;
}
}

template<class preproct, class learn_configurationt>
safety_checkert::resultt cegis_symex_learnt<preproct, learn_configurationt>::run_bmc(
    message_handlert &msg, const optionst &opt)
{
  const symbol_tablet &st=config.get_symbol_table();
  cbmc_solverst solvers(opt, st, msg);
  const std::unique_ptr<cbmc_solverst::solvert> solver=solvers.get_solver();
  bmct bmc(opt, st, msg, solver->prop_conv());

  const safety_checkert::resultt bmc_result=bmc(config.get_goto_functions());
  if (safety_checkert::UNSAFE != bmc_result) return bmc_result;
  const goto_tracet &trace=bmc.safety_checkert::error_trace;
  config.process(counterexamples, current_solution_size);
  config.convert(current_candidate, trace, current_solution_size);
  return safety_checkert::UNSAFE;
}

namespace
{
// TODO: Detect automatically
#define FULL_WIDTH 32u
#define CEGIS_LIMIT_WORDSIZE "cegis-limit-wordsize"
#define WIDTH_OPT "cegis-word-width"

size_t calculate_word_width(const optionst &options)
{
  if (!options.get_bool_option(CEGIS_LIMIT_WORDSIZE)) return FULL_WIDTH;
  return options.get_unsigned_int_option(WIDTH_OPT);
}
}

template<class preproct, class learn_configurationt>
bool cegis_symex_learnt<preproct, learn_configurationt>::learn_at_current_size()
{
  word_width=calculate_word_width(options);
  null_message_handlert msg;
  optionst o(options);
  o.set_option("unwinding-assertions", false);
  const symbol_tablet &st=config.get_symbol_table();
  const goto_functionst &gf=config.get_goto_functions();
  safety_checkert::resultt full_width_result=safety_checkert::ERROR;
  goto_tracet full_width_trace;
  for (; word_width < FULL_WIDTH; word_width*=2)
  {
    config.process(counterexamples, current_solution_size);
    config.set_word_width(word_width);
    const safety_checkert::resultt limited_result=run_bmc(msg, o);
    if (safety_checkert::UNSAFE == limited_result) return true;
    if (safety_checkert::ERROR == limited_result) return false;
    if (safety_checkert::ERROR == full_width_result)
    {
      config.process(counterexamples, current_solution_size);
      full_width_result=cegis_learn_run_bmc(full_width_trace, st, gf, msg, o);
      if (safety_checkert::UNSAFE != full_width_result) return false;
    }
  }
  config.process(counterexamples, current_solution_size);
  if (safety_checkert::ERROR == full_width_result) full_width_result=
      cegis_learn_run_bmc(full_width_trace, st, gf, msg, o);
  if (safety_checkert::UNSAFE != full_width_result) return false;
  config.convert(current_candidate, full_width_trace, current_solution_size);
  return true;
}

template<class preproct, class learn_configurationt>
template<class itert>
bool cegis_symex_learnt<preproct, learn_configurationt>::learn(itert first,
    const itert &last)
{
  add_counterexamples(first, last);
  if (counterexamples.empty()) return true;

  for (; current_solution_size <= max_solution_size; ++current_solution_size)
  {
    preproc(current_solution_size);
    if (learn_at_current_size()) return true;
  }
  return false;
}

template<class preproct, class learn_configurationt>
template<class itert>
void cegis_symex_learnt<preproct, learn_configurationt>::add_counterexamples(
    itert first, const itert &last)
{
  counterexamplest &ces=counterexamples;
  for (; first != last; ++first)
  {
    const counterexamplet &ce=*first;
    assert(ces.end() == std::find(ces.begin(), ces.end(), ce));
    ces.push_back(ce);
  }
}

template<class preproct, class learn_configurationt>
void cegis_symex_learnt<preproct, learn_configurationt>::show_candidate(
    messaget::mstreamt &os) const
{
  config.show_candidate(os, current_candidate);
}

template<class preproct, class learn_configurationt>
void cegis_symex_learnt<preproct, learn_configurationt>::set_solution_size_range(
    const size_t min, const size_t max)
{
  current_solution_size=std::max(current_solution_size, min);
  current_solution_size=std::min(current_solution_size, max);
  max_solution_size=max;
}
