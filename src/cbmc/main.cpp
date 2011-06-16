/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2005 Daniel Kroening <kroening@kroening.com>

*/

#include "parseoptions.h"
#include <signal_catcher.h> 

#include <cstring>
#include <sys/wait.h>

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
#if defined(_WIN32)
  cbmc_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
#else
  if((argc>1 && 0==strcmp(argv[1],"+nofork"))
      /* consider: || getpid() == getpgrp() 
       * - no signal catcher in this case */)
  {
    argv[1]=argv[0];
    cbmc_parseoptionst parseoptions(argc-1, argv+1);
    return parseoptions.main();
  }

  pid_t child=fork();
  assert(0<=child);
  child_pgid=child;
  if(0==child)
  {
    setpgid(0, getpid());
    char ** args=new char*[argc+2];
    args[0]=strdup(argv[0]);
    args[1]=strdup("+nofork");
    args[argc+1]=0;
    while(--argc>0)
      args[argc+1]=strdup(argv[argc]);
    execvp(argv[0], args);
    perror("Failed to run child");
    assert(0);
  }

  install_signal_catcher();
  int exitcode=-1;
  waitpid(child, &exitcode, 0);
  return WEXITSTATUS(exitcode);
#endif
}
