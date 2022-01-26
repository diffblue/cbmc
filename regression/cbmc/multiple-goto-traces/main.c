#include <assert.h>

int main(int argc, char **argv)
{
  assert(4 != argc);
  argc++;
  argc--;
  assert(argc >= 0);
  assert(argc != 4);
  argc++;
  argc--;
  assert(argc + 1 != 5);
  return 0;
}
