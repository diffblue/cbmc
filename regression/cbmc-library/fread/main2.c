#include <assert.h>
#include <stdio.h>

int main(void)
{
  FILE *f = fopen("/dev/null", "r");
  if(!f)
    return 0;
  char b[4];
  // C11 7.21.8.1p3: if size or nmemb is zero, fread returns zero
  size_t r = fread(b, 0, 3, f);
  assert(r == 0);
  return 0;
}
