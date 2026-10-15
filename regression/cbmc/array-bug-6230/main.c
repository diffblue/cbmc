#include <stdint.h>
#include <stdlib.h>

struct inner
{
  // 32 is the minimum to crash as it will produce an array wider than 1000 bits
  // (the default value of MAX_FLATTENED_ARRAY_SIZE)
  uint32_t exts[32];
};

struct outer
{
  struct inner ctx; // Nesting is necessary
};

int main()
{
  struct outer *s = malloc(sizeof(struct outer));
  if(s != NULL)
    s->ctx.exts[0] = 0;
}
