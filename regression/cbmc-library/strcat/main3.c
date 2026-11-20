#include <string.h>

int main(void)
{
  char buf[16] = "abc";
  // the source "bc" overlaps the bytes written to buf + 3 onwards
  strcat(buf, buf + 1);
  return 0;
}
