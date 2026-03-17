// Verify string operations from <cstring>
#include <cassert>
#include <cstring>

int main()
{
  char buf[10];
  std::memset(buf, 0, sizeof(buf));
  assert(buf[0] == 0);
  assert(buf[9] == 0);

  const char *src = "hello";
  assert(std::strlen(src) == 5);

  char dst[10];
  std::strcpy(dst, src);
  assert(std::strcmp(dst, "hello") == 0);

  return 0;
}
