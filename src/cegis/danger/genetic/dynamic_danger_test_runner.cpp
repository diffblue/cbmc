/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstdlib>

#include <cegis/instrument/literals.h>
#include <cegis/genetic/serialise_individual.h>
#include <cegis/genetic/dynamic_test_runner_helper.h>
#include <cegis/danger/genetic/dynamic_danger_test_runner.h>

dynamic_danger_test_runnert::dynamic_danger_test_runnert(
    const std::function<std::string(void)> &source_code_provider,
    const std::function<size_t(size_t)> &max_prog_sz) :
    source_code_provider(source_code_provider), max_prog_sz(max_prog_sz), shared_library(
    LIBRARY_PREFIX,
    LIBRARY_SUFFIX), handle(0), fitness_tester(0)
{
}

dynamic_danger_test_runnert::~dynamic_danger_test_runnert()
{
  close_fitness_tester_library(handle, fitness_tester);
}

void dynamic_danger_test_runnert::run_test(individualt &ind,
    const counterexamplet &ce, const std::function<void(bool)> on_complete)
{
  prepare_fitness_tester_library(handle, fitness_tester, source_code_provider,
      shared_library());
  std::deque<unsigned int> args;
  serialise(args, ce);
  serialise(args, ind, max_prog_sz);

  const int argc=args.size();
  std::vector<unsigned int> argv;
  argv.resize(argc);
  for (int i=0; i < argc; ++i)
    argv[i]=args[i];

  on_complete(EXIT_SUCCESS == fitness_tester(argv.data()));
}

void dynamic_danger_test_runnert::join()
{
}
