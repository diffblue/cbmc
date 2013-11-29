#include <stdlib.h>
#include <assert.h>

int main()
{
  char * a[] = { "   -9", "+0x42", "017", "0xa", "0xD" };

  assert(strtol(a[0], 0, 10)==-9);
  assert(strtol(a[1], 0, 0)==66);
  assert(strtol(a[1], 0, 16)==66);
  assert(strtol(a[2], 0, 0)==15);
  assert(strtol(a[2], 0, 8)==15);
  assert(strtol(a[3], 0, 0)==10);
  assert(strtol(a[3], 0, 16)==10);
  assert(strtol(a[4], 0, 0)==13);
  assert(strtol(a[4], 0, 16)==13);

  assert(strtol(a[2], 0, 32)==39);
  assert(strtol(a[4], 0, 11)==0);
  assert(strtol(a[4]+2, 0, 11)==0);
  assert(strtol(a[4]+2, 0, 15)==13);

  char * end=0;
  (void)strtol(a[0], &end, 10);
  assert(end==a[0]+5);

  assert(atoi(a[0])==-9);
  assert(atol(a[0])==-9);

  return 0;
}
