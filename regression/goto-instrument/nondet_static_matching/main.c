#include <assert.h>

int do_nondet_init1;
int init1;

int main(int argc, char **argv)
{
  static int do_nondet_init2;
  static int init2;

  assert(do_nondet_init1 == 0);
  assert(init1 == 0);
  assert(do_nondet_init2 == 0);
  assert(init2 == 0);

  return 0;
}
