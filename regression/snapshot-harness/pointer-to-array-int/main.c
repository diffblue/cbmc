#include <assert.h>
#include <malloc.h>

int *first;
int *second;
int *third;
int array_size;
const int *prefix;
int prefix_size;

void initialize()
{
  first = (int *)malloc(sizeof(int) * 5);
  first[0] = 0;
  first[1] = 1;
  first[2] = 2;
  first[3] = 3;
  first[4] = 4;
  second = first;
  array_size = 5;
  third = &array_size;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(first == second);
  // The following assertions will be check in the following PR once
  // dynamically allocated snapshots are properly implemented.
  /* assert(array_size >= prefix_size); */
  /* assert(prefix_size >= 0); */
  /* assert(second[prefix_size] != 6); */
  /* assert(second[4] == 4); */

  /* for(int i = 0; i < prefix_size; i++) */
  /*   assert(second[i] != prefix[i]); */
  return 0;
}
