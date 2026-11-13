#include <assert.h>
#ifndef _WIN32
#  include <getopt.h>
#else
extern char *optarg;
extern int optind;
int getopt(int argc, char *const argv[], const char *optstring);
#endif

int main(void)
{
  // Test that getopt advances optind after "-o file".
  char a0[] = "prog", a1[] = "-o", a2[] = "file";
  char *argv[] = {a0, a1, a2, 0};

  int c = getopt(3, argv, "o:");
  assert(c == 'o');
  // POSIX: optind shall be incremented by 2 when the option-argument
  // is in the next element.
  assert(optind == 3);

  return 0;
}
