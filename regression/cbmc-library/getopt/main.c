#include <assert.h>
#ifndef _WIN32
#  include <getopt.h>
#else
extern char *optarg;
extern int optind;
int getopt(int argc, char *const argv[], const char *optstring);
#endif
#include <stdlib.h>

int main()
{
  int argc = 3;
  char *argv[] = {"my_program", "-t", "10", NULL};

  int opt;
  int nsecs = 0;

  while((opt = getopt(argc, argv, "t:")) != -1)
  {
    switch(opt)
    {
    case 't':
      nsecs = atoi(optarg);
      break;
    default: /* '?' */
      return 1;
    }
  }

  assert(nsecs == 10);

  return 0;
}
