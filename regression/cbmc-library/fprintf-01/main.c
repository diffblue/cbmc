#include <assert.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  fprintf(stdout, "some string %s: %d\n", argv[0], 42);
  fprintf(stderr, "some other string\n");
  return 0;
}
