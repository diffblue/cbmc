#include <assert.h>
#include <string.h>

int main(void)
{
  // Non-overlapping copy within the same buffer
  char buf[16] = "abc";
  strcpy(buf + 8, buf);       // [0,4) and [8,12) do not overlap
  assert(buf[8] == (char)97); // a
  assert(buf[11] == 0);
  return 0;
}
