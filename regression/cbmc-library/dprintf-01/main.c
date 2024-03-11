#include <assert.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  dprintf(1, "some string %s: %d\n", argv[0], 42);
  dprintf(1, "some other string\n");
  return 0;
}
