#include <assert.h>
#include <stdint.h>

#pragma pack(push, 1)
struct S
{
  uint32_t a;
  uint64_t c;
  uint32_t d;
};
#pragma pack(pop)

int main()
{
  struct S s;
  uint64_t v;
  // The store covers bytes 8..15, straddling the end of member c (bytes 4..11)
  // and the start of member d (bytes 12..15).
  *(uint64_t *)((char *)&s + 8) = v;
  for(int i = 0; i < 8; ++i)
    assert(((uint8_t *)&s)[8 + i] == ((uint8_t *)&v)[i]);
  return 0;
}
