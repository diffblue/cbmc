/* FUNCTION: _getopt */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

char *optarg = NULL;
int optind = 1;

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
size_t __VERIFIER_nondet_size_t(void);

int _getopt(int argc, char *const argv[], const char *optstring)
{
__CPROVER_HIDE:;
  // re-init requested by environment, we just reset optind
  if(optind == 0)
    optind = 1;

  // test whether all arguments have been processed
  if(optind >= argc)
    return -1;
  char *const arg = argv[optind];
  if(arg[0] != '-' || arg[1] == '\0' || (arg[1] == '-' && arg[2] == '\0'))
    return -1;

  // test whether the option is in optstring at all
  size_t optstring_len = strlen(optstring);
  // gcc doesn't know __CPROVER_forall
#ifndef LIBRARY_CHECK
  __CPROVER_bool not_found = __CPROVER_forall
  {
    size_t i;
    i<optstring_len ==> optstring[i] != arg[1]
  };
  if(not_found)
    return '?';
#endif

  // option is in optstring, find the exact index
  size_t result_index = __VERIFIER_nondet_size_t();
  __CPROVER_assume(
    result_index < optstring_len && optstring[result_index] == arg[1]);
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(
    __CPROVER_is_zero_string(optstring),
    "getopt zero-termination of 3rd argument");
#endif

  // is an argument required?
  if(result_index + 1 == optstring_len || optstring[result_index + 1] != ':')
  {
    optarg = NULL;
    return arg[1];
  }

  // test whether a required argument can be found
  if(arg[2] != '\0')
  {
    optarg = &arg[2];
    return arg[1];
  }
  else if(optind + 1 < argc)
  {
    optarg = argv[optind + 1];
    ++optind;
    return arg[1];
  }
  else
  {
    optarg = NULL;
    return optstring[0] == ':' ? ':' : '?';
  }
}

/* FUNCTION: getopt */

int _getopt(int argc, char *const argv[], const char *optstring);

int getopt(int argc, char *const argv[], const char *optstring)
{
__CPROVER_HIDE:;
  return _getopt(argc, argv, optstring);
}

/* FUNCTION: getopt_long */

#ifndef _WIN32
// MSVC doesn't provide getopt.h, which we need for struct option

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

#endif
