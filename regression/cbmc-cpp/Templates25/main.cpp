#include <cassert>
template <class, int>
bool True()
{
  return true;
}

int main()
{
  bool result = True<int, 0>();
  assert(result == true);
}
