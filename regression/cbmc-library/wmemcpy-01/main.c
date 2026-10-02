#include <assert.h>
#include <wchar.h>

int main()
{
  // C11 7.29.4.2.3 / 7.29.4.2.4 / 7.29.4.6.2 / 7.29.4.6.1: wmemcpy,
  // wmemmove and wmemset copy or set wide characters; wcslen counts them
  // (libstdc++'s char_traits<wchar_t>::copy, move, assign and length)
  wchar_t s[3] = {L'a', L'b', 0};
  wchar_t d[3];
  wmemcpy(d, s, 3);
  assert(d[1] == L'b');
  wmemmove(d, d + 1, 2);
  assert(d[0] == L'b');
  wmemset(d, L'x', 2);
  assert(d[1] == L'x');
  assert(wcslen(s) == 2);
  assert(wmemcmp(s, s, 2) == 0);
  return 0;
}
