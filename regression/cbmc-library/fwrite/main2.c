#include <assert.h>
#include <stdio.h>

int main(void)
{
  char b[4] = "abc";
  // C11 7.21.8.2p3: if size or nmemb is zero, fwrite returns zero
  size_t r = fwrite(b, 0, 3, stdout);
  assert(r == 0);
  return 0;
}
