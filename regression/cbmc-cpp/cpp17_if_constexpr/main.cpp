#include <cassert>

template <bool B>
int pick()
{
  if constexpr(B)
    return 1;
  else
    return 2;
}

int main()
{
  assert(pick<true>() == 1);
  assert(pick<false>() == 2);
  return 0;
}
