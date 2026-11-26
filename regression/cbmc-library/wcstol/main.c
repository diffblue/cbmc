#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t s[6] = L" 42x";
  wchar_t *end;
  assert(wcstol(s, &end, 10) == 42);
  assert(end == s + 3);
  assert(wcstol(L"ff", 0, 16) == 255);
  assert(*end == L'4');
  return 0;
}
