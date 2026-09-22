// std::find over a std::vector<int> with libstdc++ 16 under -std=c++20:
// the iterator returned points outside the vector's storage
// ("dereference failure: pointer outside object bounds in
// *return_value_forward<ref_const_signed_int>", <bits/stl_algo.h>'s
// __find_if through std::__invoke).  The same program verifies with gcc 13's
// headers.
#include <algorithm>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> v = {1, 2, 3};
  auto it = std::find(v.begin(), v.end(), 2);
  __CPROVER_assert(it != v.end() && *it == 2, "find");
  return 0;
}
