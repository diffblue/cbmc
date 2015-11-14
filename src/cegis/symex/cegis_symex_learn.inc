#include <iterator>

#include <goto-programs/safety_checker.h>

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>

template<class learn_configurationt>
cegis_symex_learnt<learn_configurationt>::cegis_symex_learnt(
    const optionst &options, learn_configurationt &config) :
    options(options), config(config), max_solution_size(1u)
{
}

template<class learn_configurationt>
cegis_symex_learnt<learn_configurationt>::~cegis_symex_learnt()
{
}

template<class learn_configurationt>
const typename cegis_symex_learnt<learn_configurationt>::candidatet &cegis_symex_learnt<
    learn_configurationt>::next_candidate() const
{
  return current_candidate;
}

template<class learn_configurationt>
bool cegis_symex_learnt<learn_configurationt>::learn(
    const size_t max_solution_size)
{
  this->max_solution_size=max_solution_size;
  return learn(counterexamples.end(), counterexamples.end());
}

template<class learn_configurationt>
template<class itert>
bool cegis_symex_learnt<learn_configurationt>::learn(itert first,
    const itert &last)
{
  std::copy(first, last, std::back_inserter(counterexamples));
  if (counterexamples.empty()) return true;
  config.process(counterexamples, max_solution_size);

  null_message_handlert msg;
  optionst learn_options(options);
  learn_options.set_option("unwinding-assertions", false);
  const symbol_tablet &st=config.get_symbol_table();
  cbmc_solverst solvers(learn_options, st, msg);
  const std::unique_ptr<cbmc_solverst::solvert> solver=solvers.get_solver();
  bmct bmc(learn_options, st, msg, solver->prop_conv());

  const safety_checkert::resultt bmc_result=bmc(config.get_goto_functions());
  if (safety_checkert::UNSAFE != bmc_result) return false;
  const goto_tracet &trace=bmc.safety_checkert::error_trace;
  config.convert(current_candidate, trace, max_solution_size);
  return true;
}

template<class learn_configurationt>
void cegis_symex_learnt<learn_configurationt>::show_candidate(
    messaget::mstreamt &os) const
{
  config.show_candidate(os, current_candidate);
}
