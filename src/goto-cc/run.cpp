/*******************************************************************\

Module: 

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/

#ifdef _WIN32
#include <process.h>
#else

#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include <sys/wait.h>
#include <sys/types.h>

#endif

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

  char **_argv=new char * [argv.size()+1];

  for(unsigned i=0; i<argv.size(); i++)
    _argv[i]=argv[i].c_str();
  
  int status=_spawn(_P_WAIT, what.c_str(), _argv);

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
      for(unsigned i=0; i<argv.size(); i++)
        _argv[i]=strdup(argv[i].c_str());

      _argv[argv.size()]=NULL;
      
      execvp(what.c_str(), _argv);
      /* usually no return */
      return 1;
    }
    else /* fork() returns new pid to the parent process */
    {
      int status;     /* parent process: child's exit status */
      wait(&status); /* wait for child to exit, and store its status */
      return WEXITSTATUS(status);
    }
  }
  else /* fork returns -1 on failure */
    return 1;
  #endif
}
