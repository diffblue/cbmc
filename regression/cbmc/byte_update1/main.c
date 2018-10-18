#include <assert.h>

struct A {
  int x;
};

int main(int argc, char** argv) {

  struct A a;
  int i;
  struct A* a_addr=&a;

  if(argc != 2)
    return;

  void** ptrs[argc];
  for(i = 0; i < 2; ++i)
    ptrs[i] = (void*)0;

  ((struct A**)ptrs)[1]=&a;
  assert(ptrs[1] == (void*)&a);

}
