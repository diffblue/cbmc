#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t a[4] = L"abc";
  assert(wmemchr(a, L'b', 3) == a + 1);
  assert(wmemchr(a, L'd', 3) == 0);
  assert(wmemchr(a, L'c', 2) != 0);
  return 0;
}
