#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t a[3] = L"ab", b[3];
  assert(wmemcpy(b, a, 3) == b);
  assert(b[0] == L'a' && b[1] == L'b' && b[2] == 0);
  assert(b[1] == L'a');
  return 0;
}
