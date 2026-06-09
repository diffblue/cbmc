#include <assert.h>

struct s
{
  char buf[8];
};

int main(void)
{
  struct s a;

  // __builtin_has_attribute is conservatively modelled as false (CBMC does
  // not track GCC attributes).  Both the bare-name and name-with-arguments
  // forms must parse.
  int b1 = __builtin_has_attribute(a.buf, nonstring);
  int b2 = __builtin_has_attribute(a.buf, counted_by(8));

  assert(b1 == 0);
  assert(b2 == 0);

  // mirrors the Linux fortify-string strscpy _Static_assert pattern, which
  // asserts a buffer is a NUL-terminated C-string (i.e. NOT __nonstring).
  _Static_assert(
    !(!(!__builtin_has_attribute(a.buf, nonstring))), "must be C-string");

  return a.buf[0];
}
