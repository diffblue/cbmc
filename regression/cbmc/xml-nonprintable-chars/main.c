#include <assert.h>

int main(void)
{
  const unsigned char *str = (unsigned char *)"\x00";
  assert(*str == '\x01');
  return 0;
}
