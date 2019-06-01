#include <assert.h>
#include <stdlib.h>
#include <string.h>

void test_simplified()
{
  unsigned char a[6];

  unsigned len_b;
  __CPROVER_assume(len_b > 0 && len_b < 3);
  unsigned char *b = malloc(len_b);

  memcpy(a + 2, b, len_b);
  assert(a[2] == b[0]);
}

void test_full()
{
  size_t capacity;
  unsigned char *a = malloc(capacity);

  size_t len_b;
  __CPROVER_assume(len_b < 10);
  unsigned char *b = malloc(len_b);

  size_t len_a;
  __CPROVER_assume(len_a < 10);

  if(len_a + len_b < capacity)
  {
    memcpy(a + len_a, b, len_b);
  }

  unsigned char *c = a + len_a;

  if(len_b > 0 && len_a + len_b < capacity)
  {
    size_t i;
    __CPROVER_assume(i < len_b);
    assert(c[i] == b[i]);
  }
}

int main()
{
  test_simplified();
  test_full();

  return 0;
}
