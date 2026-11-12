#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t a[3] = L"ab", b[3] = L"ac";
  assert(wmemcmp(a, b, 1) == 0);
  assert(wmemcmp(a, b, 2) < 0);
  assert(wmemcmp(b, a, 2) == 0);
  return 0;
}
