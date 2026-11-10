#include <cassert>
template <typename T>
struct Box
{
  T val;
};
template <typename T>
using BoxOf = Box<T>;
int main()
{
  BoxOf<int> b;
  b.val = 42;
  assert(b.val == 42);
  return 0;
}
