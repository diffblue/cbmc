#include <assert.h>

volatile char zero_to_unlock;

void busy_wait (void) {
  while (zero_to_unlock);
  return;
}

int main (int argc, char **argv) {
  // Obviously we would need to spawn some other threads here...
  
  zero_to_unlock = 1;
  busy_wait();

  assert(0);
  
  return 0;
}
