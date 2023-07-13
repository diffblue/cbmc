#include <assert.h>

#define ARRAY_SIZE 10000

int main()
{
  struct my_structt
  {
    int eggs;
    int ham;
  };
  struct my_structt struct_array[ARRAY_SIZE];
  int x;
  __CPROVER_assume(x > 0 && x < ARRAY_SIZE);
  struct_array[x].eggs = 3;
  assert(struct_array[x].eggs + struct_array[x].ham != 10);
  assert(struct_array[x].eggs + struct_array[x].ham != 11);
}
