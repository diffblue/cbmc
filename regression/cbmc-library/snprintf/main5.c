#include <assert.h>
#include <stdio.h>
#include <wchar.h>

int main(void)
{
  char b[8];
  // C11 7.21.6.5p3: a negative value if an encoding error occurred, as
  // converting a wide character may cause
  int r = snprintf(b, sizeof b, "x%lsy", L"z");
  assert(r >= 0); // must FAIL
  r = snprintf(b, sizeof b, "%d", 1);
  assert(r == 1);
  return 0;
}
