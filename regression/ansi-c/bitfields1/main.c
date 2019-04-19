#include <limits.h>

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#if CHAR_BIT == 8
struct bits
{
  char a : 4;
  char b : 4;
  char c : 4;
  char d : 4;
  int i;
};

STATIC_ASSERT(sizeof(struct bits) == 2 * sizeof(int));

#pragma pack(1)
struct packed_bits
{
  char a : 4;
  char b : 4;
  char c : 4;
  char d : 4;
  int i;
};
#pragma pack()

STATIC_ASSERT(sizeof(struct packed_bits) == sizeof(int) + 2);
#endif

int main()
{
}
