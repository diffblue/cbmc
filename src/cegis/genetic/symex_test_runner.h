/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_GENETIC_SYMEX_TEST_RUNNER_H
#define CPROVER_CEGIS_GENETIC_SYMEX_TEST_RUNNER_H

#include <util/expr.h>

#include <cegis/value/program_individual.h>

#ifdef _WIN32
typedef int pid_t;
#endif

template<class configt>
class symex_test_runnert
{
public:
  typedef std::map<const irep_idt, exprt> counterexamplet;
  typedef program_individualt individualt;
private:
  class bool_pipet
  {
#ifndef _WIN32
    int fd[2u];
#endif
    individualt *individual;
  public:
    pid_t child_pid;
    explicit bool_pipet(individualt *individual);
    void run_test(const class optionst &options, configt &config,
        const counterexamplet &ce);
    void join();
  };
  typedef std::deque<bool_pipet> taskst;
  taskst tasks;
  const optionst &options;
  configt &config;

  void cleanup();
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param config
   */
  symex_test_runnert(const optionst &options, configt &config);

  /**
   * @brief
   *
   * @details
   */
  ~symex_test_runnert();

  /**
   * @brief
   *
   * @details
   *
   * @param ind
   * @param ce
   */
  void run_test(individualt &ind, const counterexamplet &ce);

  /**
   * @brief
   *
   * @details
   */
  void join();
};

#include "symex_test_runner.inc"

#endif // CPROVER_CEGIS_GENETIC_SYMEX_TEST_RUNNER_H
