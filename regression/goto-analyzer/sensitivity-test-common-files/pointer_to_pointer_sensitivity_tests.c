#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent pointers to pointers
  // Basic use of addresses
  int a=0;
  int *p=&a;
  int **x=&p;

  // Reading from a pointer to a pointer that's been dereferenced twice
  assert(**x==0);
  assert(**x==1);
  a=1;
  assert(**x==1);
  assert(**x==0);

  // Writing to a pointer to a pointer that's been dereferenced twice
  **x=2;
  assert(a==2);
  assert(a==1);

  return 0;
}
