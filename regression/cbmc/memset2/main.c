#include <string.h>
#include <assert.h>

typedef struct {
  int a;
  int b;
} TEST;

static TEST test;

main()
{
  test.a = 1;
  test.b = 2;
  memset(&test.b, 0, sizeof(test.b));
  assert(test.a);
  assert(!test.b);
  test.b = 2;
  memset(&test.a, 0, sizeof(test.a));
  assert(!test.a);
  assert(test.b);
}
