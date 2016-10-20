#include <goto-programs/safety_checker.h>
#include <cegis/cegis-util/cbmc_runner.h>

template<class verify_configurationt>
cegis_symex_verifyt<verify_configurationt>::cegis_symex_verifyt(
    const optionst &options, verify_configurationt &config) :
    options(options), config(config), is_failure(true)
{
}

template<class verify_configurationt>
cegis_symex_verifyt<verify_configurationt>::~cegis_symex_verifyt()
{
}

safety_checkert::resultt run_cegis_symex(goto_tracet &trace,
    const optionst &options, const class symbol_tablet &st,
    const class goto_functionst &gf);

template<class verify_configurationt>
void cegis_symex_verifyt<verify_configurationt>::verify(
    const candidatet &candidate)
{
  is_failure=true;
  current_counterexamples.clear();
  config.process(candidate);
  const symbol_tablet &st=config.get_symbol_table();
  const goto_functionst &gf=config.get_goto_functions();
  cbmc_resultt cbmc_result;
  const safety_checkert::resultt result=run_cbmc(st, gf, cbmc_result, options);
  switch (result)
  {
  case safety_checkert::SAFE:
    is_failure=false;
  case safety_checkert::ERROR:
    return;
  default:
    config.convert(current_counterexamples, cbmc_result.trace);
  }
}

template<class verify_configurationt>
typename cegis_symex_verifyt<verify_configurationt>::const_iterator cegis_symex_verifyt<
    verify_configurationt>::counterexamples_begin() const
{
  return current_counterexamples.begin();
}

template<class verify_configurationt>
typename cegis_symex_verifyt<verify_configurationt>::const_iterator cegis_symex_verifyt<
    verify_configurationt>::counterexamples_end() const
{
  return current_counterexamples.end();
}

template<class verify_configurationt>
bool cegis_symex_verifyt<verify_configurationt>::has_counterexamples() const
{
  return !current_counterexamples.empty();
}

template<class verify_configurationt>
bool cegis_symex_verifyt<verify_configurationt>::success() const
{
  return !is_failure;
}

template<class verify_configurationt>
void cegis_symex_verifyt<verify_configurationt>::show_counterexample(
    messaget::mstreamt &os, const counterexamplet &counterexample) const
{
  config.show_counterexample(os, counterexample);
}
