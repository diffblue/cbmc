#include <assert.h>

struct S1
{
  int a : 2;
  __attribute__((aligned(16))) int b : 32;
  int c : 32;
  __attribute__((aligned(8))) int d : 2;
  int e : 30;
  __attribute__((aligned(16))) int f : 2;
  __attribute__((aligned(8))) int g : 2;
};

struct S1 s1;

int main()
{
  assert(sizeof(s1) == 48);
  return 0;
}
