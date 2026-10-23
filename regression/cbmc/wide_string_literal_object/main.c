// C11 6.4.5/6: a wide string literal initializes an array of static storage
// duration; a pointer to its first element reaches every element
#include <assert.h>
#include <wchar.h>
int main()
{
  const wchar_t *p = L"ab";
  assert(p[0] == L'a' && p[1] == L'b' && p[2] == 0);
  return 0;
}
