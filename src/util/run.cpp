/*******************************************************************\

Module:

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/

#include "run.h"

#include <cassert>

#ifdef _WIN32
#include <process.h>
#else

#include <cstring>
#include <unistd.h>
#include <cerrno>
#include <cstdio>
#include <cstdlib>

#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <signal.h>

#endif

#include <util/unicode.h>
#include <util/signal_catcher.h>

int run_shell(const std::string &command)
{
  std::string shell="/bin/sh";
  std::vector<std::string> argv;
  argv.push_back(shell);
  argv.push_back(command);
  return run(shell, argv, "", "");
}

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output)
{
  #ifdef _WIN32
  // we don't support stdin/stdout redirection on Windows
  assert(std_input.empty());
  assert(std_output.empty());

  // unicode version of the arguments
  std::vector<std::wstring> wargv;

  wargv.resize(argv.size());

  for(std::size_t i=0; i<argv.size(); i++)
    wargv[i]=widen(argv[i]);

  std::vector<const wchar_t *> _argv(argv.size()+1);

  for(std::size_t i=0; i<wargv.size(); i++)
    _argv[i]=wargv[i].c_str();

  _argv[argv.size()]=NULL;

  // warning: the arguments may still need escaping

  std::wstring wide_what=widen(what);

  int status=_wspawnvp(_P_WAIT, wide_what.c_str(), _argv.data());

  return status;

  #else
  int stdin_fd=STDIN_FILENO;

  if(!std_input.empty())
  {
    stdin_fd=open(std_input.c_str(), O_RDONLY);
    if(stdin_fd==-1)
    {
      perror("Failed to open stdin copy");
      return 1;
    }
  }

  int stdout_fd=STDOUT_FILENO;

  if(!std_output.empty())
  {
    stdout_fd=open(std_output.c_str(), O_CREAT|O_WRONLY, S_IRUSR|S_IWUSR);
    if(stdout_fd==-1)
    {
      perror("Failed to open stdout copy");
      return 1;
    }
  }

  // temporarily suspend all signals
  sigset_t new_mask, old_mask;
  sigemptyset(&new_mask);
  sigprocmask(SIG_SETMASK, &new_mask, &old_mask);

  /* now create new process */
  pid_t childpid = fork();

  if(childpid>=0) /* fork succeeded */
  {
    if(childpid==0) /* fork() returns 0 to the child process */
    {
      // resume signals
      remove_signal_catcher();
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      std::vector<char *> _argv(argv.size()+1);
      for(std::size_t i=0; i<argv.size(); i++)
        _argv[i]=strdup(argv[i].c_str());

      _argv[argv.size()]=nullptr;

      if(stdin_fd!=STDIN_FILENO)
        dup2(stdin_fd, STDIN_FILENO);
      if(stdout_fd!=STDOUT_FILENO)
        dup2(stdout_fd, STDOUT_FILENO);
      execvp(what.c_str(), _argv.data());

      /* usually no return */
      return 1;
    }
    else /* fork() returns new pid to the parent process */
    {
      // resume signals
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      int status;     /* parent process: child's exit status */

      /* wait for child to exit, and store its status */
      while(waitpid(childpid, &status, 0)==-1)
        if(errno==EINTR)
          continue; // try again
        else
        {
          perror("Waiting for child process failed");
          if(stdin_fd!=STDIN_FILENO)
            close(stdin_fd);
          if(stdout_fd!=STDOUT_FILENO)
            close(stdout_fd);
          return 1;
        }

      if(stdin_fd!=STDIN_FILENO)
        close(stdin_fd);
      if(stdout_fd!=STDOUT_FILENO)
        close(stdout_fd);

      return WEXITSTATUS(status);
    }
  }
  else /* fork returns -1 on failure */
  {
    // resume signals
    sigprocmask(SIG_SETMASK, &old_mask, nullptr);

    if(stdin_fd!=STDIN_FILENO)
      close(stdin_fd);
    if(stdout_fd!=STDOUT_FILENO)
      close(stdout_fd);

    return 1;
  }
  #endif
}
