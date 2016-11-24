#include <assert.h>

int main() {
  const int N=2;
  int outlist[N]; // N will be type cast to long
  int result=outlist[0]; // initializer in declaration
  assert(result==42);

  return 0;
}
