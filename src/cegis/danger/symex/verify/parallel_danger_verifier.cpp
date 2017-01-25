/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#ifndef _WIN32
#include <unistd.h>
#endif

#include <cegis/symex/cegis_symex_verify.h>

#include <cegis/danger/symex/verify/restrict_counterexamples.h>
#include <cegis/danger/symex/verify/parallel_danger_verify_task.h>
#include <cegis/danger/symex/verify/parallel_danger_verifier.h>

parallel_danger_verifiert::parallel_danger_verifiert(const optionst &options,
    danger_verify_configt &config) :
    options(options), config(config), is_failure(true)
{
}

parallel_danger_verifiert::~parallel_danger_verifiert()
{
}

void parallel_danger_verifiert::verify(const candidatet &candidate)
{
  all_ces.clear();
  config.process(candidate);
  parallel_danger_verify_poolt pool(all_ces, options, config, candidate);
  pool.schedule(parallel_danger_verify_taskt::FULL);
  pool.schedule(parallel_danger_verify_taskt::RANKING);
  pool.schedule(parallel_danger_verify_taskt::ASSERTION);
  is_failure=!pool.join();
}

parallel_danger_verifiert::const_iterator parallel_danger_verifiert::counterexamples_begin() const
{
  return all_ces.begin();
}

parallel_danger_verifiert::const_iterator parallel_danger_verifiert::counterexamples_end() const
{
  return all_ces.end();
}

bool parallel_danger_verifiert::has_counterexamples() const
{
  return !all_ces.empty();
}

bool parallel_danger_verifiert::success() const
{
  return !is_failure;
}

void parallel_danger_verifiert::show_counterexample(messaget::mstreamt &os,
    const counterexamplet &counterexample) const
{
  config.show_counterexample(os, counterexample);
}
