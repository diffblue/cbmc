#include <assert.h>

void recurse_down_from(int x) {
  if(x > 0)
    recurse_down_from(x - 1);
}

int main(int argc, char **argv) {
  for(int i = 0; i < 10; ++i) {
    if(i == argc)
      break;
  }
  recurse_down_from(10);

  assert(0);
}
