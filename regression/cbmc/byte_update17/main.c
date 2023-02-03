#include <inttypes.h>
#include <string.h>

// a union that is exactly one byte wide
union U
{
  unsigned char c;
};

int main()
{
  unsigned char size;
  __CPROVER_assume(size > 1);
  __CPROVER_assume(size < 5);
  __CPROVER_assume(size % 4 == 0);
  union U u[size];
  u[0].c = 42;
  u[1].c = 42;
  u[2].c = 42;
  u[3].c = 42;
  int32_t dest;
  memcpy(&dest, u, size);
  __CPROVER_assert(dest == 42 | 42 << 8 | 42 << 16 | 42 << 24, "");
}
