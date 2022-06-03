/* FUNCTION: getopt */

extern char *optarg;
extern int optind;

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
size_t __VERIFIER_nondet_size_t();

int getopt(int argc, char *const argv[], const char *optstring)
{
  __CPROVER_HIDE:;
  int result=-1;

  if(optind==0)
    optind=1;

  if(optind>=argc || argv[optind][0]!='-')
    return -1;

  size_t result_index=__VERIFIER_nondet_size_t();
  __CPROVER_assume(
    result_index<strlen(optstring) && optstring[result_index]!=':');
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(optstring),
    "getopt zero-termination of 3rd argument");
  #endif

  __CPROVER_bool found=__VERIFIER_nondet___CPROVER_bool();
  if(found)
  {
    result=optstring[result_index];
    __CPROVER_bool skipped=__VERIFIER_nondet___CPROVER_bool();
    if(skipped)
      ++optind;
  }

  if(result!=-1 && optind<argc && optstring[result_index+1]==':')
  {
    __CPROVER_bool has_no_arg=__VERIFIER_nondet___CPROVER_bool();
    if(has_no_arg)
    {
      optarg=argv[optind];
      ++optind;
    }
    else
      optarg=NULL;
  }

  return result;
}

/* FUNCTION: getopt_long */

#ifndef __CPROVER_GETOPT_H_INCLUDED
#include <getopt.h>
#define __CPROVER_GETOPT_H_INCLUDED
#endif

int getopt_long(
  int argc,
  char *const argv[],
  const char *optstring,
  const struct option *longopts,
  int *longindex)
{
  // trigger valid-pointer checks (if enabled), even though we don't
  // use the parameter in this model
  (void)*longopts;
  // avoid unused-parameter warnings when compiling using GCC (for
  // internal library syntax checks)
  (void)longindex;

  return getopt(argc, argv, optstring);
}
