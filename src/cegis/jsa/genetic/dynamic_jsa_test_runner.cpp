/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <cstdlib>

#include <cegis/cegis-util/module_helper.h>
#include <cegis/genetic/dynamic_test_runner_helper.h>
#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/converters/counterexample.h>
#include <cegis/jsa/genetic/dynamic_jsa_test_runner.h>

dynamic_jsa_test_runnert::dynamic_jsa_test_runnert(
    const std::function<std::string(void)> &source_code_provider) :
    source_code(source_code_provider), shared_library(LIBRARY_PREFIX,
    LIBRARY_SUFFIX), handle(0), fitness_tester(0)
{
}

dynamic_jsa_test_runnert::~dynamic_jsa_test_runnert()
{
  close_fitness_tester_library(handle, fitness_tester);
}

std::string get_compile_options()
{
  std::string path("-I ");
  const std::string exe(get_current_executable_file_path());
  path+=exe.substr(0, exe.rfind("cegis", exe.rfind("cegis") - 1) - 1);
  return path+=' ';
}

void dynamic_jsa_test_runnert::run_test(individualt &individual,
    const counterexamplet &counterexample,
    const std::function<void(bool)> on_complete)
{
  const std::string lib(shared_library());
  const std::string opt(get_compile_options());
  prepare_fitness_tester_library(handle, fitness_tester, source_code, lib, opt);

  const individualt::queryt &query=individual.query;
  const std::size_t jsa_query_size=query.size();
  std::vector<__CPROVER_jsa_query_instructiont> jsa_query;
  jsa_query.resize(jsa_query_size);
  size_t index=0;
  for(const individualt::queryt::value_type &instr : query)
    jsa_query[index++]=instr;

  const individualt::invariantt &invariant=individual.invariant;
  const __CPROVER_jsa_index_t jsa_invariant_size=__CPROVER_jsa_index_t(invariant.size());
  std::vector<__CPROVER_jsa_invariant_instructiont> jsa_invariant;
  jsa_invariant.resize(jsa_invariant_size);
  index=0;
  for(const individualt::invariantt::value_type &instr : invariant)
    jsa_invariant[index++]=instr;

  const individualt::predicatest &preds=individual.predicates;
  const size_t num_preds=preds.size();
  std::vector<__CPROVER_jsa_index_t> jsa_predicate_sizes;
  jsa_predicate_sizes.reserve(num_preds);
  std::vector<std::vector<__CPROVER_jsa_pred_instructiont> > jsa_predicates;
  jsa_predicates.reserve(num_preds);
  std::vector<const __CPROVER_jsa_pred_instructiont *> jsa_predicates_arg;
  for(const individualt::predicatet &pred : preds)
  {
    jsa_predicates.push_back(decltype(jsa_predicates)::value_type());
    for(const individualt::predicatet::value_type &instr : pred)
      jsa_predicates.back().push_back(instr);

    jsa_predicates_arg.push_back(jsa_predicates.back().data());
    jsa_predicate_sizes.push_back(__CPROVER_jsa_index_t(pred.size()));
  }

  const std::size_t num_heaps=count_heaps(counterexample);
  std::vector<__CPROVER_jsa_abstract_heapt> heaps;
  heaps.resize(num_heaps);
  retrieve_heaps(counterexample, heaps.data());

  const std::size_t num_words=count_words(counterexample);
  std::vector<__CPROVER_jsa_word_t> words;
  words.resize(num_words);
  retrieve_words(counterexample, words.data());

  on_complete(EXIT_SUCCESS == fitness_tester(
      jsa_query_size, jsa_query.data(),
      jsa_invariant_size,
      jsa_invariant.data(),
      jsa_predicate_sizes.data(),
      jsa_predicates_arg.data(),
      heaps.data(),
      words.data()));
}

void dynamic_jsa_test_runnert::join()
{
}
