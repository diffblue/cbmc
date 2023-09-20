#include <assert.h>
#include <time.h>

int main()
{
  char dest[3];
  struct tm input;
  size_t result = strftime(dest, 3, "%y", &input);
  assert(result < 3);
  return 0;
}
