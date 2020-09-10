#include <assert.h>

#define CODE_BLOCK                                                             \
  int i;                                                                       \
  float flotal = 0;                                                            \
  for(i = 0; i < n; ++i)                                                       \
  {                                                                            \
    flotal += i;                                                               \
  }                                                                            \
  assert(flotal == (n * (n - 1) / 2))

void do_the_loop(int n)
{
  CODE_BLOCK;
}

int main(int argc, char **argv)
{
  int j;

  // Will give unknown unless the bound is over 25
  for(j = 0; j < 5; j++)
  {
    int n = 5;
    CODE_BLOCK;
  }

  // Paths in the loop will merge but that is OK
  // because the value of n is the important bit
  for(j = 0; j < 1000; j++)
  {
    int n = 10;
    do_the_loop(n);
  }

  return 0;
}
