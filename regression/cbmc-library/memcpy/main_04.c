#include <stdlib.h>
#include <string.h>

typedef struct
{
  size_t len;
  char *name;
} info_t;

void publish(info_t *info)
{
  size_t size;
  __CPROVER_assume(size >= info->len);
  unsigned char *buffer = malloc(size);
  memcpy(buffer, info->name, info->len);
  if(info->len > 42)
  {
    __CPROVER_assert(buffer[42] == 42, "should pass");
    __CPROVER_assert(buffer[41] == 42, "should fail");
  }
}

void main()
{
  info_t info;
  size_t name_len;
  info.name = malloc(name_len);
  info.len = name_len;
  if(name_len > 42)
    info.name[42] = 42;
  publish(&info);
}
