#include <stdint.h>
#include <stdlib.h>

typedef struct
{
  uint8_t *buf;
  size_t size;
} blob;

void foo(blob *b, uint8_t *value)
  // clang-format off
__CPROVER_requires(b->size == 5)
__CPROVER_assigns(__CPROVER_POINTER_OBJECT(b->buf))
__CPROVER_assigns(__CPROVER_POINTER_OBJECT(value))
__CPROVER_ensures(b->buf[0] == 1)
__CPROVER_ensures(b->buf[1] == 1)
__CPROVER_ensures(b->buf[2] == 1)
__CPROVER_ensures(b->buf[3] == 1)
__CPROVER_ensures(b->buf[4] == 1)
// clang-format on
{
  b->buf[0] = *value;
  b->buf[1] = *value;
  b->buf[2] = *value;
  b->buf[3] = *value;
  b->buf[4] = *value;

  *value = 2;
}

int main()
{
  blob b;
  b.size = 5;
  b.buf = malloc(b.size * (sizeof(*(b.buf))));
  uint8_t value = 1;

  foo(&b, &value);

  return 0;
}
