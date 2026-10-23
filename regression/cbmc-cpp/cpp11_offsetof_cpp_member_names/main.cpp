#include <stddef.h>
typedef struct
{
  unsigned len;
  unsigned char d;
} S1; // anonymous, typedef'd, not packed
typedef struct
{
  unsigned len;
  unsigned char d;
} __attribute__((__packed__)) S2;
struct S3
{
  unsigned len;
  unsigned char d;
} __attribute__((__packed__));
using A1 = S1;
using A2 = S2;
using A3 = S3;
static_assert(offsetof(S1, d) == 4, "S1");
static_assert(offsetof(A1, d) == 4, "A1 alias of anon typedef");
static_assert(offsetof(S2, d) == 4, "S2 packed typedef");
static_assert(offsetof(A2, d) == 4, "A2 alias of anon packed typedef");
static_assert(offsetof(A3, d) == 4, "A3 alias of named packed");
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(offsetof(A2, d) == 4, "runtime offsetof through alias");
  return 0;
}
