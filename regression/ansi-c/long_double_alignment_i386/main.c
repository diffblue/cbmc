#include <stddef.h>

struct LD
{
  char c;
  long double d;
};

// the declaration of max_align_t in GCC's and Clang's stddef.h uses
// __attribute__((__aligned__(__alignof__(long double))))
_Static_assert(sizeof(max_align_t) > 0, "");
_Static_assert(sizeof(long double) == 12, "");
_Static_assert(_Alignof(long double) == 4, "");
_Static_assert(sizeof(struct LD) == 16, "");
_Static_assert(offsetof(struct LD, d) == 4, "");

int main()
{
  return 0;
}
