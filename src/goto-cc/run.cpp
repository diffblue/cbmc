/*******************************************************************\

Module: 

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/

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

#endif

#include <util/unicode.h>

#include "run.h"
  
/*******************************************************************\

Function: run

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
int run(
  const std::string &what,
  const std::vector<std::string> &argv)
{
  #ifdef _WIN32
  // unicode version of the arguments
  std::vector<std::wstring> wargv;
  
  wargv.resize(argv.size());
  
  for(std::size_t i=0; i<argv.size(); i++)
    wargv[i]=widen(argv[i]);

  const wchar_t **_argv=new const wchar_t * [argv.size()+1];

  for(std::size_t i=0; i<wargv.size(); i++)
    _argv[i]=wargv[i].c_str();
  
  _argv[argv.size()]=NULL;

  // warning: the arguments may still need escaping

  std::wstring wide_what=widen(what);

  int status=(int)_wspawnvp(_P_WAIT, wide_what.c_str(), _argv);

  delete[] _argv;  

  return status;
  
  #else
  pid_t childpid; /* variable to store the child's pid */

  /* now create new process */
  childpid = fork();
    
  if(childpid>=0) /* fork succeeded */
  {
    if(childpid==0) /* fork() returns 0 to the child process */
    {
      char **_argv=new char * [argv.size()+1];
      for(std::size_t i=0; i<argv.size(); i++)
        _argv[i]=strdup(argv[i].c_str());

      _argv[argv.size()]=NULL;
      
      execvp(what.c_str(), _argv);
      /* usually no return */
      return 1;
    }
    else /* fork() returns new pid to the parent process */
    {
      int status;     /* parent process: child's exit status */

      while(waitpid(childpid, &status, 0)==-1) /* wait for child to exit, and store its status */
        if(errno==EINTR)
          continue; // try again
        else
        {
          perror("Waiting for child process failed");
          return 1;
        }

      return WEXITSTATUS(status);
    }
  }
  else /* fork returns -1 on failure */
    return 1;
  #endif
}
