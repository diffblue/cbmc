#include <algorithm>
#include <array>
#include <cassert>
#include <cfloat>
#include <climits>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <initializer_list>
#include <limits>
#include <list>
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <stack>
#include <tuple>
#include <type_traits>
#include <typeinfo>
#include <utility>
#include <valarray>
#include <vector>

namespace A::B::C
{
int x = 42;
}

int main()
{
  assert(A::B::C::x == 42);
  static_assert(std::is_same<int, int>::value, "");
  return 0;
}
