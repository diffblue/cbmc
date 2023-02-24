#include <assert.h>

void empty_loop (void) {
 loop : goto loop;
  return;
}

int main (int argc, char **argv) {
  empty_loop();

  assert(0);
  
  return 0;
}
