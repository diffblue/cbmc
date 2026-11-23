#include <assert.h>
#include <stdio.h>

int main()
{
  // %n stores the number of characters output so far, also those that do
  // not fit the buffer
  char b[4];
  int n = 0;
  signed char hh = 0;
  long long ll = 0;
  int r = snprintf(b, sizeof b, "abcdef%n|%d%hhn%lln", &n, 42, &hh, &ll);
  assert(r == 9 && n == 6 && hh == 9 && ll == 9);
  return 0;
}
