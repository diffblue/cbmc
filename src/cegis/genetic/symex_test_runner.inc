#include <algorithm>

#ifndef _WIN32
#include <cstdlib>
#include <unistd.h>
#include <sys/wait.h>
#endif

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>

#ifndef _WIN32
#define BOOL_PIPE "bool_pipe"
#define FORK "fork"
#endif

template<class configt>
symex_test_runnert<configt>::bool_pipet::bool_pipet(individualt *individual) :
    individual(individual), child_pid(0u)
{
}

template<class configt>
void symex_test_runnert<configt>::bool_pipet::run_test(
    const class optionst &options, configt &config, const counterexamplet &ce)
{
#ifndef _WIN32
  if (pipe(fd))
  {
    perror(BOOL_PIPE);
    throw std::runtime_error("Error creating pipe.");
  }
  child_pid=fork();
  if (-1 == child_pid)
  {
    perror(FORK);
    throw std::runtime_error("Error forking process.");
  }
  if (child_pid)
  {
    close(fd[1u]);
    return;
  }
  close(fd[0u]);
#endif
  danger_goto_solutiont converted;
  config.convert(converted, *individual);
  config.set_candidate(converted);
  null_message_handlert msg;
  config.set_test_case(ce);
  const symbol_tablet &st=config.get_symbol_table();
  cbmc_solverst solvers(options, st, msg);
  const goto_functionst &gf=config.get_goto_functions();
  const std::unique_ptr<cbmc_solverst::solvert> solver=solvers.get_solver();
  bmct bmc(options, st, msg, solver->prop_conv());
  const unsigned char is_safe=(safety_checkert::SAFE == bmc(gf));
#ifdef _WIN32
  if (is_safe) ++individual->fitness;
#else
  ssize_t result;
  do
  {
    result=write(fd[1u], &is_safe, sizeof(unsigned char));
  } while (result == 0);
  if (result == -1)
  {
    perror(BOOL_PIPE);
    throw std::runtime_error("Error writing to pipe.");
  }
  close(fd[1u]);
  exit(EXIT_SUCCESS);
#endif
}

template<class configt>
void symex_test_runnert<configt>::bool_pipet::join()
{
#ifndef _WIN32
  ssize_t result;
  unsigned char is_safe;
  do
  {
    result=read(fd[0u], &is_safe, sizeof(unsigned char));
    if (result == -1)
    {
      perror(BOOL_PIPE);
      throw std::runtime_error("Error reading pipe.");
    }
  } while (result == 0);
  close(fd[0u]);
  if (is_safe) ++individual->fitness;
#endif
}

template<class configt>
symex_test_runnert<configt>::symex_test_runnert(const optionst &options,
    configt &config) :
    options(options), config(config)
{
}

template<class configt>
symex_test_runnert<configt>::~symex_test_runnert()
{
}

#ifndef _WIN32
namespace
{
#define MAX_CHILDREN 200u

pid_t wait_child(int &status, const size_t size)
{
  const int options=size < MAX_CHILDREN ? WNOHANG : 0;
  return waitpid(-1, &status, options);
}
}
#endif

template<class configt>
void symex_test_runnert<configt>::cleanup()
{
#ifndef _WIN32
  std::deque<pid_t> t;
  int status;
  for (pid_t child_pid=wait_child(status, tasks.size()); child_pid > 0;
      child_pid=wait_child(status, tasks.size()))
  {
    assert(WIFEXITED(status) && EXIT_SUCCESS == WEXITSTATUS(status));
    t.push_back(child_pid);
  }
  tasks.erase(std::remove_if(tasks.begin(), tasks.end(), [&t](bool_pipet &task)
  {
    if(std::find(t.begin(), t.end(), task.child_pid) != t.end())
    {
      task.join();
      return true;
    }
    return false;}), tasks.end());
#endif
}

template<class configt>
void symex_test_runnert<configt>::run_test(individualt &individual,
    const counterexamplet &ce)
{
  cleanup();
  bool_pipet pipe(&individual);
#ifndef _WIN32
  tasks.push_back(pipe);
  tasks.back().run_test(options, config, ce);
#else
  pipe.run_test(options, config, ce);
#endif
}

template<class configt>
void symex_test_runnert<configt>::join()
{
#ifndef _WIN32
  for (bool_pipet &task : tasks)
  {
    int status;
    waitpid(task.child_pid, &status, 0);
    assert(WIFEXITED(status) && EXIT_SUCCESS == WEXITSTATUS(status));
    task.join();
  }
  tasks.clear();
#endif
}
