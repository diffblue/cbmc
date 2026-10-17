#include <cassert>
#include <memory>
int main()
{
  std::unique_ptr<int> p(new int(42));
  assert(*p == 42);
  return 0;
}
