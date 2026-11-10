#include <string.h>

int main()
{
  char buf[4] = {'a', 'b', 'c', 'd'};
  // reads past the end of buf, as 'z' does not occur in it
  memchr(buf, 'z', 5);
  return 0;
}
