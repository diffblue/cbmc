/*******************************************************************\

Module:

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/

#include "run.h"

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

#include <util/invariant.h>
#include <util/unicode.h>
#include <util/signal_catcher.h>

int run(const std::string &what, const std::vector<std::string> &argv)
{
  return run(what, argv, "", "", "");
}

#ifndef _WIN32
/// open given file to replace either stdin, stderr, stdout
static int stdio_redirection(int fd, const std::string &file)
{
  int result_fd = fd;

  if(file.empty())
    return result_fd;

  int flags = 0, mode = 0;
  std::string name;

  switch(fd)
  {
  case STDIN_FILENO:
    flags = O_RDONLY;
    name = "stdin";
    break;

  case STDOUT_FILENO:
  case STDERR_FILENO:
    flags = O_CREAT | O_WRONLY;
    mode = S_IRUSR | S_IWUSR;
    name = fd == STDOUT_FILENO ? "stdout" : "stderr";
    break;

  default:
    UNREACHABLE;
  }

  result_fd = open(file.c_str(), flags, mode);
  if(result_fd == -1)
    perror(("Failed to open " + name + " file " + file).c_str());

  return result_fd;
}
#endif

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output,
  const std::string &std_error)
{
  #ifdef _WIN32
  // we use the cmd.exe shell to do stdin/stdout/stderr redirection on Windows
  if(!std_input.empty() || !std_output.empty() || !std_error.empty())
  {
    std::vector<std::string> new_argv = argv;
    new_argv.insert(new_argv.begin(), "cmd.exe");
    new_argv.insert(new_argv.begin() + 1, "/c");

    if(!std_input.empty())
    {
      new_argv.push_back("<");
      new_argv.push_back(std_input);
    }

    if(!std_output.empty())
    {
      new_argv.push_back(">");
      new_argv.push_back(std_output);
    }

    if(!std_error.empty())
    {
      new_argv.push_back("2>");
      new_argv.push_back(std_error);
    }

    // this is recursive
    return run(new_argv[0], new_argv, "", "", "");
  }

  // unicode version of the arguments
  std::vector<std::wstring> wargv;

  wargv.resize(argv.size());

  for(std::size_t i=0; i<argv.size(); i++)
    wargv[i]=widen(argv[i]);

  std::vector<const wchar_t *> _argv(argv.size()+1);

  for(std::size_t i=0; i<wargv.size(); i++)
    _argv[i]=wargv[i].c_str();

  _argv[argv.size()]=NULL;

  // warning: the arguments may still need escaping,
  // as windows will concatenate the argv strings back together,
  // separating them with spaces

  std::wstring wide_what=widen(what);
  int status=_wspawnvp(_P_WAIT, wide_what.c_str(), _argv.data());
  return status;

  #else
  int stdin_fd = stdio_redirection(STDIN_FILENO, std_input);
  int stdout_fd = stdio_redirection(STDOUT_FILENO, std_output);
  int stderr_fd = stdio_redirection(STDERR_FILENO, std_error);

  if(stdin_fd == -1 || stdout_fd == -1 || stderr_fd == -1)
    return 1;

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
      if(stderr_fd != STDERR_FILENO)
        dup2(stderr_fd, STDERR_FILENO);

      errno=0;
      execvp(what.c_str(), _argv.data());

      /* usually no return */
      perror(std::string("execvp "+what+" failed").c_str());
      exit(1);
    }
    else /* fork() returns new pid to the parent process */
    {
      // must do before resuming signals to avoid race
      register_child(childpid);

      // resume signals
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      int status;     /* parent process: child's exit status */

      /* wait for child to exit, and store its status */
      while(waitpid(childpid, &status, 0)==-1)
      {
        if(errno==EINTR)
          continue; // try again
        else
        {
          unregister_child();

          perror("Waiting for child process failed");
          if(stdin_fd!=STDIN_FILENO)
            close(stdin_fd);
          if(stdout_fd!=STDOUT_FILENO)
            close(stdout_fd);
          if(stderr_fd != STDERR_FILENO)
            close(stderr_fd);
          return 1;
        }
      }

      unregister_child();

      if(stdin_fd!=STDIN_FILENO)
        close(stdin_fd);
      if(stdout_fd!=STDOUT_FILENO)
        close(stdout_fd);
      if(stderr_fd != STDERR_FILENO)
        close(stderr_fd);

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
    if(stderr_fd != STDERR_FILENO)
      close(stderr_fd);

    return 1;
  }
  #endif
}
