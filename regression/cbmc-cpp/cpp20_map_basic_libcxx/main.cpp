// C++20 <map> header
#include <map>
int main()
{
  std::map<int, int> m;
  m[1] = 42;
  __CPROVER_assert(m[1] == 42, "map access");
}
