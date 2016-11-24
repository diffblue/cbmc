/*******************************************************************\

Module: CBMC Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  CBMC
  Bounded Model Checking for ANSI-C
  Copyright (C) 2001-2014 Daniel Kroening <kroening@kroening.com>

*/

#include <util/unicode.h>

#ifdef IREP_HASH_STATS
#include <iostream>
#endif

#include "cbmc_parse_options.h"
#include <util/signal_catcher.h>
#include <stdio.h>
#include <unistd.h>

#include <cstring>
#include <sys/wait.h>

/*******************************************************************\

Function: main / wmain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef IREP_HASH_STATS
extern unsigned long long irep_hash_cnt;
extern unsigned long long irep_cmp_cnt;
extern unsigned long long irep_cmp_ne_cnt;
#endif

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
#else
int main(int argc, const char **argv)
{
#endif
#if defined(_WIN32)
  cbmc_parse_optionst parse_options(argc, argv);

  int res=parse_options.main();

  #ifdef IREP_HASH_STATS
  std::cout << "IREP_HASH_CNT=" << irep_hash_cnt << std::endl;
  std::cout << "IREP_CMP_CNT=" << irep_cmp_cnt << std::endl;
  std::cout << "IREP_CMP_NE_CNT=" << irep_cmp_ne_cnt << std::endl;
  #endif

  return res;
#else
  if((argc>1 && 0==strcmp(argv[1],"+nofork"))
      /* consider: || getpid() == getpgrp()
       * - no signal catcher in this case */)
  {
    argv[1]=argv[0];
    cbmc_parse_optionst parse_options(argc-1, argv+1);

    int res=parse_options.main();

    #ifdef IREP_HASH_STATS
    std::cout << "IREP_HASH_CNT=" << irep_hash_cnt << std::endl;
    std::cout << "IREP_CMP_CNT=" << irep_cmp_cnt << std::endl;
    std::cout << "IREP_CMP_NE_CNT=" << irep_cmp_ne_cnt << std::endl;
    #endif

    return res;
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
