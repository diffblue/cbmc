#include <assert.h>

int main()
{
  // __builtin_LINE() returns the current line number
  assert(__builtin_LINE() == 6);

  // __builtin_FUNCTION() returns the enclosing function name
  const char *fn = __builtin_FUNCTION();
  assert(fn[0] == 'm');
  assert(fn[1] == 'a');
  assert(fn[2] == 'i');
  assert(fn[3] == 'n');
  assert(fn[4] == 0);

  // __builtin_FILE() returns a non-null string
  const char *f = __builtin_FILE();
  assert(f != 0);

  return 0;
}
