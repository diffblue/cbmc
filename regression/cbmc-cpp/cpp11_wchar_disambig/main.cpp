#include <cassert>

// Two overloads differing by char vs wchar_t, simulating
// std::endl<char> and std::endl<wchar_t>.
int process(char c)
{
  return 1;
}
int process(wchar_t w)
{
  return 2;
}

typedef int (*char_fn)(char);

int main()
{
  // Using 'process' as a function pointer value (no call arguments)
  // triggers ambiguity between the char and wchar_t overloads.
  // The resolver should prefer the char variant.
  char_fn fn = process;
  assert(fn('a') == 1);
  return 0;
}
