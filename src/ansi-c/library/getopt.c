/* FUNCTION: getopt */

extern char *optarg;

inline int getopt(int argc, char * const argv[],
                  const char *optstring)
{
  __CPROVER_HIDE:;
  unsigned result_index;
  __CPROVER_assume(result_index<argc);
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(optstring),
    "getopt zero-termination of 3rd argument");
  #endif
  optarg = argv[result_index];
}
