#include <assert.h>
#include <string.h>

int main()
{
  const char s[] = "abcabc";
  // C23 7.26.5.8: the FIRST occurrence; an empty needle matches at once
  assert(strstr(s, "bc") == s + 1);
  assert(strstr(s, "cab") == s + 2);
  assert(strstr(s, "abc") == s);
  assert(strstr(s, "") == s);
  assert(strstr(s, "abd") == 0);
  assert(strstr(s, "abcabcx") == 0);
  assert(strstr("", "") != 0);
  return 0;
}
