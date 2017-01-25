/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFY_TASK_H
#define CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFY_TASK_H

#include <cegis/cegis-util/irep_pipe.h>
#include <cegis/danger/symex/verify/danger_verify_config.h>

#ifdef _WIN32
typedef int pid_t;
#endif

/**
 * @brief
 *
 * @details
 */
class parallel_danger_verify_taskt
{
public:
  typedef enum
  {
    FULL=0, RANKING=1, ASSERTION=2
  } modet;
  typedef danger_verify_configt::candidatet candidatet;
  typedef std::set<danger_verify_configt::counterexamplet> counterexamplest;
private:
  const class optionst &options;
  danger_verify_configt &config;
  const candidatet &candidate;
  const modet mode;
  danger_verify_configt::counterexamplest new_ces;
  bool success;
  irep_pipet pipe;
  pid_t child_pid;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param options
   * @param config
   * @param candidate
   * @param mode
   */
  parallel_danger_verify_taskt(const optionst &options,
      danger_verify_configt &config, const candidatet &candidate, modet mode);

  /**
   * @brief
   *
   * @details
   *
   * @param other
   */
  explicit parallel_danger_verify_taskt(const parallel_danger_verify_taskt &other);

  /**
   * @brief
   *
   * @details
   */
  ~parallel_danger_verify_taskt();

  /**
   * @brief
   *
   * @details
   */
  void operator()();

  /**
   * @brief
   *
   * @details
   *
   * @param child_pid
   */
  void set_parent_mode(pid_t child_pid);

  /**
   * @brief
   *
   * @details
   *
   * @param success
   * @param counterexamples
   */
  void read_counterexamples(bool &success, counterexamplest &counterexamples);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  pid_t get_child_pid() const;
};

/**
 * @brief
 *
 * @details
 */
class parallel_danger_verify_poolt
{
public:
  typedef parallel_danger_verify_taskt::counterexamplest counterexamplest;
  typedef parallel_danger_verify_taskt::candidatet candidatet;
private:
  counterexamplest &ces;
  const optionst &options;
  danger_verify_configt &config;
  const candidatet &candidate;
  std::deque<parallel_danger_verify_taskt> tasks;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param counterexamples
   * @param options
   * @param config
   * @param candidate
   */
  parallel_danger_verify_poolt(counterexamplest &counterexamples,
      const optionst &options, danger_verify_configt &config,
      const candidatet &candidate);

  /**
   * @brief
   *
   * @details
   */
  ~parallel_danger_verify_poolt();

  /**
   * @brief
   *
   * @details
   *
   * @param config
   * @param mode
   */
  void schedule(parallel_danger_verify_taskt::modet mode);

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  bool join();
};

#endif // CPROVER_CEGIS_DANGER_SYMEX_VERIFY_PARALLEL_DANGER_VERIFY_TASK_H
