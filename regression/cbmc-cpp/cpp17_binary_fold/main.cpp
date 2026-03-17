// C++17: binary fold expressions (init op ... op pack)
#include <cassert>

template <typename... Args>
int sum(Args... args)
{
  return (0 + ... + args);
}

template <typename... Args>
bool all_positive(Args... args)
{
  return (... && (args > 0));
}

int main()
{
  assert(sum(1, 2, 3, 4) == 10);
  assert(all_positive(1, 2, 3));
  assert(!all_positive(1, -2, 3));
}
