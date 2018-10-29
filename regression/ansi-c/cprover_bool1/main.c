#define STATIC_ASSERT(condition) int some_array##__LINE__[(condition) ? 1 : -1]

struct bits
{
  __CPROVER_bool b1;
  __CPROVER_bool b2;
  __CPROVER_bool b3;
  __CPROVER_bool b4;
  __CPROVER_bool b5;
  __CPROVER_bool b6;
  __CPROVER_bool b7;
  __CPROVER_bool b8;
  int i;
};

STATIC_ASSERT(sizeof(struct bits) == 2 * sizeof(int));

#include <limits.h>

#if CHAR_BIT >= 8
#pragma pack(1)
struct packed_bits
{
  __CPROVER_bool b1;
  __CPROVER_bool b2;
  __CPROVER_bool b3;
  __CPROVER_bool b4;
  __CPROVER_bool b5;
  __CPROVER_bool b6;
  __CPROVER_bool b7;
  __CPROVER_bool b8;
  int i;
};
#pragma pack()

STATIC_ASSERT(sizeof(struct packed_bits) == sizeof(int) + 1);
#endif

// a _Bool is at least one byte wide
STATIC_ASSERT(sizeof(_Bool[CHAR_BIT]) >= CHAR_BIT);
// __CPROVER_bool is just a single bit
STATIC_ASSERT(sizeof(__CPROVER_bool[CHAR_BIT]) == 1);

int main()
{
}
