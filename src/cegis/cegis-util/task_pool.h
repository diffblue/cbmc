/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_TASK_POOL_H
#define CPROVER_CEGIS_CEGIS_UTIL_TASK_POOL_H

#ifndef _WIN32
#include <unistd.h>
#endif
#include <functional>
#include <map>
#include <set>

/**
 * @brief Task pool implementation.
 *
 * @details Uses fork() on Linux.
 * XXX: Not supported on Windows.
 */
class task_poolt
{
public:
#ifndef _WIN32
  typedef pid_t task_idt;
#else
  typedef size_t task_idt;
#endif
  typedef std::set<task_idt> task_idst;
  typedef std::function<int(void)> taskt;
  typedef std::function<void(int)> on_completet;
  typedef std::map<task_idt, on_completet> handlerst;
private:
  task_idst task_ids;
  handlerst handlers;
public:
  /**
   * @brief Creates a task pool
   *
   * @details Creates an empty task pool
   */
  task_poolt();

  /**
   * @brief Default destructor.
   *
   * @details Closes all remaining pipes.
   */
  ~task_poolt();

  /**
   * @brief Schedules a task.
   *
   * @details Schedules a task without pipe.
   *
   * @param task The task to run.
   */
  task_idt schedule(const taskt &task);

  /**
   * @brief
   *
   * @details
   *
   * @param task
   * @param on_complete
   *
   * @return
   */
  task_idt schedule(const taskt &task, const on_completet &on_complete);

  /**
   * @brief
   *
   * @details
   *
   * @param id
   */
  void cancel(task_idt id);

  /**
   * @brief Joins a task.
   *
   * @details Waits for the given task to complete.
   *
   * @param id The task to wait for.
   */
  void join(task_idt id);

  /**
   * @brief Joins all tasks.
   *
   * @details Waits for all scheduled tasks to complete.
   */
  void join_all();

  /**
   * @brief Joins already terminated tasks.
   *
   * @details Joins termianted tasks and executes their handlers, but
   * doesn't block.
   */
  void join_some();
};

#endif // CPROVER_CEGIS_CEGIS_UTIL_TASK_POOL_H
