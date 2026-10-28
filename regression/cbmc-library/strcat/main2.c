#include <assert.h>
#include <string.h>

int main(void)
{
  char buf[16] = "ab";
  buf[8] = 0;
  // [buf + 8, buf + 10] and [buf, buf + 2] do not overlap
  strcat(buf + 8, buf);
  assert(buf[8] == 97);
  assert(buf[10] == 0);
  return 0;
}
