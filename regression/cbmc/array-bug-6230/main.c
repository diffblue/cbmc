#include <stdint.h>
#include <stdlib.h>

struct inner
{
  uint32_t exts[32]; // 32 is the minimum to crash
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
