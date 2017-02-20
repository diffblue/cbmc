/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef _WIN32
#include <signal.h>
#include <sys/signal.h>
#include <sys/wait.h>
#endif

#include <algorithm>
#include <cstdlib>
#include <iterator>
#include <sstream>

#include <util/irep.h>

#include <cegis/cegis-util/task_pool.h>

task_poolt::task_poolt()
{
}

task_poolt::~task_poolt()
{
}

#ifdef _WIN32
#define NOT_SUPPORTED() assert(!"task_poolt not supported on Windows.")
#endif

namespace
{
#ifndef _WIN32
void execute_and_remove(task_poolt::handlerst &handlers, const pid_t pid,
    const int status)
{
  const task_poolt::handlerst::iterator it=handlers.find(pid);
  if(handlers.end() != it)
  {
    it->second(status);
    handlers.erase(it);
  }
}
#endif

void cleanup(task_poolt::task_idst &task_ids, task_poolt::handlerst &handlers)
{
#ifndef _WIN32
  std::map<task_poolt::task_idt, int> joined;
  int status;
  for(pid_t child_pid=waitpid(-1, &status, WNOHANG); child_pid > 0; child_pid=
      waitpid(-1, &status, WNOHANG))
    joined.insert(std::make_pair(child_pid, status));
  for(const std::pair<task_poolt::task_idt, int> &task : joined)
  {
    const task_poolt::task_idt id=task.first;
    execute_and_remove(handlers, id, task.second);
    task_ids.erase(id);
  }
#else
  NOT_SUPPORTED();
#endif
}

#ifndef _WIN32
bool erase_if_managed(task_poolt::task_idst &ids, const task_poolt::task_idt id)
{
  const task_poolt::task_idst::iterator task_id=ids.find(id);
  if(ids.end() == task_id) return false;
  ids.erase(task_id);
  return true;
}
#endif
}

#define FORK_ERROR "Fork system call failed."

task_poolt::task_idt task_poolt::schedule(const taskt &task)
{
  cleanup(task_ids, handlers);
#ifndef _WIN32
  const pid_t child_pid=fork();
  if(child_pid == -1)
  {
    perror(FORK_ERROR);
    throw std::runtime_error(FORK_ERROR);
  }
  if(child_pid)
  {
    task_ids.insert(child_pid);
    return child_pid;
  }
  setpgid(child_pid, 0);
  try
  {
    exit(task());
  } catch (...)
  {
    exit(EXIT_FAILURE);
  }
#else
  NOT_SUPPORTED();
  return 0;
#endif
}

task_poolt::task_idt task_poolt::schedule(const taskt &task,
    const on_completet &on_complete)
{
  cleanup(task_ids, handlers);
  const task_poolt::task_idt id=schedule(task);
  handlers.insert(std::make_pair(id, on_complete));
  return id;
}

#define MAX_WAIT 5u

void task_poolt::cancel(const task_idt id)
{
#ifndef _WIN32
  if(!erase_if_managed(task_ids, id)) return;
  int status;
  size_t wait_count=0;
  do
  {
    kill(id, SIGTERM);
    usleep(20000);
  } while(!waitpid(id, &status, WNOHANG) && ++wait_count < MAX_WAIT);
  if(wait_count >= MAX_WAIT)
  {
    kill(id, SIGKILL);
    waitpid(id, &status, 0);
  }
  execute_and_remove(handlers, id, status);
#else
  NOT_SUPPORTED();
#endif
}

void task_poolt::join(const task_idt id)
{
#ifndef _WIN32
  if(!erase_if_managed(task_ids, id)) return;
  int status;
  waitpid(id, &status, 0);
  execute_and_remove(handlers, id, status);
#else
  NOT_SUPPORTED();
#endif
}

void task_poolt::join_all()
{
#ifndef _WIN32
  const size_t num_children=task_ids.size();
  int status;
  for(size_t i=0; i < num_children; ++i)
  {
    const pid_t pid=waitpid(-1, &status, 0);
    assert(pid > 0);
    execute_and_remove(handlers, pid, status);
  }
  task_ids.clear();
  assert(handlers.empty());
#else
  NOT_SUPPORTED();
#endif
}

void task_poolt::join_some()
{
#ifndef _WIN32
  cleanup(task_ids, handlers);
#else
  NOT_SUPPORTED();
#endif
}
