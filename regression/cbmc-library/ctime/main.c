#include <assert.h>
#include <string.h>
#include <time.h>

int main(void)
{
  time_t t = 0;
  char *s = ctime(&t);
  // C11 7.27.3.2: equivalent to asctime; 26-byte buffer.
  assert(strlen(s) <= 25);
  return 0;
}
