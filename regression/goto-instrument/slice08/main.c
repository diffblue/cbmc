#include <assert.h>

int main (void) 
{
  int x;
  int i;

  if (x > 0) {
    for (i = 0; i < x; ++i) {
        // Do nothing;
    }
  } else {
    x = 1;
  }

  assert(x >= 1);

  return 0;
}

