// Test that pthread_key_create returns process-wide unique keys.
// Two threads each creating a key must get distinct values.
#include <assert.h>
#include <pthread.h>

// Communicate the child's key via a shared plain integer, not via a
// pointer argument to pthread_key_create (which CBMC flags as unsound
// in concurrency mode).
unsigned long child_key_val;

void *child(void *arg)
{
  pthread_key_t k;
  pthread_key_create(&k, 0);
  // Write the key value (an integer) to a shared variable after the
  // pthread_key_create call completes.
  child_key_val = (unsigned long)k;
  return 0;
}

int main(void)
{
  pthread_key_t main_key;
  pthread_t t;

  pthread_create(&t, 0, child, 0);
  pthread_key_create(&main_key, 0);
  pthread_join(t, 0);

  // After join, child_key_val holds the child's key.
  // Keys from different threads must be distinct.
  assert((unsigned long)main_key != child_key_val);

  return 0;
}
