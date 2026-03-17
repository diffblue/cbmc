#include <cassert>
namespace Outer
{
inline namespace V1
{
int x = 1;
}
} // namespace Outer
int main()
{
  assert(Outer::x == 1);
  assert(Outer::V1::x == 1);
  return 0;
}
