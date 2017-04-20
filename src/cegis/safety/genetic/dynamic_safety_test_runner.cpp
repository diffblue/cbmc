/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstdlib>

#include <util/substitute.h>

#include <cegis/genetic/serialise_individual.h>
#include <cegis/genetic/dynamic_test_runner_helper.h>
#include <cegis/safety/value/safety_goto_ce.h>
#include <cegis/safety/genetic/dynamic_safety_test_runner.h>

dynamic_safety_test_runnert::dynamic_safety_test_runnert(
    const std::function<std::string(void)> &source_code_provider,
    const std::function<size_t(size_t)> &max_prog_sz) :
    source_code_provider(source_code_provider), max_prog_sz(max_prog_sz), shared_library(
    LIBRARY_PREFIX,
    LIBRARY_SUFFIX), handle(0), fitness_tester(0)
{
}

dynamic_safety_test_runnert::~dynamic_safety_test_runnert()
{
  close_fitness_tester_library(handle, fitness_tester);
}

void dynamic_safety_test_runnert::run_test(individualt &ind,
    const counterexamplet &ce, const std::function<void(bool)> on_complete)
{
  const auto source_code_provider=
      [this]()
      {
        std::string code(this->source_code_provider());
        substitute(code, "unsigned int __CPROVER_cegis_deserialise_index=__CPROVER_cegis_first_prog_offset", "unsigned int __CPROVER_cegis_deserialise_index=0");
        substitute(code, "unsigned int __CPROVER_cegis_ce_index=0u", "unsigned int __CPROVER_cegis_ce_index=__CPROVER_cegis_deserialise_index");
        return code;
      };
  prepare_fitness_tester_library(handle, fitness_tester, source_code_provider,
      shared_library());
  assert(ind.x0.empty());
  std::deque<unsigned int> args;
  // TODO: Implement for multiple loops (change constraint, instrumentation)
  assert(ind.programs.size() == 1u);
  serialise(args, ind, max_prog_sz);
  serialise(args, ce.x0);
  // TODO: Implement for multiple loops (change constraint, instrumentation)
  assert(ce.x.size() == 1u);
  serialise(args, ce.x.front());

  const int argc=args.size();
  std::vector<unsigned int> argv;
  argv.resize(argc);
  for(int i=0; i < argc; ++i)
    argv[i]=args[i];

  on_complete(EXIT_SUCCESS == fitness_tester(argv.data()));
}

void dynamic_safety_test_runnert::join()
{
}
