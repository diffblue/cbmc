#include <assert.h>
// C23 6.7.2.2: enumerations with a fixed underlying type
enum G : long long
{
  GA = -1,
  GB = 0x100000000LL
};
enum U : unsigned int
{
  UA = 1,
  UBIG = 0x80000000u
};
int main(void)
{
  enum G g = GB;
  enum U u = UBIG;
  // g + 1 == 0x100000001, not 1 (if truncated to int).
  assert(g + 1 != 1);
  // u is unsigned 0x80000000, so u > 0.
  assert(u > 0);
  return 0;
}
