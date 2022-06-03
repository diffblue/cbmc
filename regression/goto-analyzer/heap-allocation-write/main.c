#include <stdlib.h>

int main()
{
  int *i_was_malloced = malloc(sizeof(int) * 10);
  int *alias = i_was_malloced;

  *i_was_malloced = 99;
  assert(*alias == 99);

  i_was_malloced[0] = 100;
  assert(*alias == 100);

  *alias += 1;
  assert(i_was_malloced[0] == 101);

  i_was_malloced[1] = 102;
  assert(alias[1] == 102);
}
