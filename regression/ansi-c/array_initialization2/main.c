#include <assert.h>

int a[(int)(10./1.)];
int b[(int)2] = { 10, 20 };
int c[(int)(10./1.)] = { 10, 20 };
int d[(int)(10/1)] = { 10, 20 };

int main (void) {
  if (a[0]) {
    assert(b[1] + c[2] > 20);
  }

  return 1;
}

extern int g_array[];
int array[(int)(10./1)];

int array2[(int)(10./1)];
