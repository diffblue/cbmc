#include <assert.h>
#include <stdlib.h>

int main()
{
  char *end;
  assert(strtoll("998", 0, 10) == 998ll);
  assert(strtoll("-42", 0, 10) == -42ll);
  assert(strtoll("ff", &end, 16) == 255ll);
  assert(strtoll("12x", &end, 10) == 12ll);
  assert(*end == 'x');
  return 0;
}
