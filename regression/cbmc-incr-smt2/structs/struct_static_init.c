#include <assert.h>
#include <stdint.h>

struct F
{
  uint16_t w;
  uint16_t x;
};

static struct F a = {0xdeadbeef};
static struct F b = {0xbeefdead};

int main()
{
  struct F *p;
  if(nondet_int())
    p = &a;
  else
    p = &b;

  assert(p->w != 0xdead);
}
