#include <assert.h>

int main() {
  unsigned int* s_pdt = (unsigned int*)(0xdeadbeef);
  assert(s_pdt > 1);
  return 0;
}

