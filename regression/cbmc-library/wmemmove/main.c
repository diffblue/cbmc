#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t a[4] = L"abc";
  wmemmove(a + 1, a, 2);
  assert(a[0] == L'a' && a[1] == L'a' && a[2] == L'b');
  wmemmove(a, a + 1, 2);
  assert(a[0] == L'a' && a[1] == L'b');
  assert(a[2] == L'c');
  return 0;
}
