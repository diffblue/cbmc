#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct nettle_buffer
{
  uint8_t *contents;
  size_t alloc;
  uint8_t condition;
  size_t size;
};

void nettle_buffer_init(struct nettle_buffer *buffer)
{
  buffer->contents = 0;
  buffer->alloc = 0;
  buffer->condition = 0;
  buffer->size = 0;
}

int nettle_buffer_grow(struct nettle_buffer *buffer, size_t length)
{
  if(buffer->condition)
    return 0; // Uncommenting this line fixes the bug.

  size_t alloc = buffer->alloc * 2 + length +
                 100; // Replcing alloc size by a constant fixes the bug.
  //size_t alloc = 103;
  uint8_t *p = (uint8_t *)malloc(alloc);
  buffer->contents = p;
  buffer->alloc = alloc;
  return 1;
}

int nettle_buffer_write(
  struct nettle_buffer *buffer,
  size_t length,
  const uint8_t *data)
{
  memcpy(buffer->contents, data, length);
  return 1;
}

int main(void)
{
  struct nettle_buffer buffer;
  nettle_buffer_init(&buffer);
  nettle_buffer_grow(&buffer, 3);
  __CPROVER_assert(buffer.size == 0, "buffer.size == 0");
  __CPROVER_assert(buffer.alloc == 103, "buffer.alloc == 103");
  __CPROVER_assert(
    nettle_buffer_write(&buffer, 3, "foo"),
    "nettle_buffer_write(&buffer, 3, \"foo\")");
  __CPROVER_assert(buffer.contents[0] == 'f', "buffer.contents[0] == 'f'");
  __CPROVER_assert(buffer.contents[1] == 'o', "buffer.contents[1] == 'o'");
  __CPROVER_assert(buffer.contents[2] == 'o', "buffer.contents[2] == 'o'");
}
