#include <assert.h>
#include <wchar.h>

int main()
{
  wchar_t a[3];
  assert(wmemset(a, L'x', 3) == a);
  assert(a[0] == L'x' && a[1] == L'x' && a[2] == L'x');
  assert(a[0] == L'y');
  return 0;
}
