#include <assert.h>
#include <string.h>

int main()
{
  const char s[] = "hello";
  // C23 7.26.5.5: the first character of s that occurs in the second string
  assert(strpbrk(s, "ol") == s + 2);
  assert(strpbrk(s, "h") == s);
  assert(strpbrk(s, "xyz") == 0);
  assert(strpbrk(s, "") == 0);
  return 0;
}
