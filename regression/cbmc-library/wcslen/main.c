#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t s[4] = L"abc";
  assert(wcslen(s) == 3);
  s[1] = 0;
  assert(wcslen(s) == 1);
  assert(wcslen(s) == 3);
  return 0;
}
