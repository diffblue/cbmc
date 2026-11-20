// std::map with libstdc++ 16 under -std=c++20: the element is stored
// (size() == 1) but neither operator[] nor count() finds it again -- the key
// comparison path selected by the C++20 headers (three-way comparison /
// _Rb_tree::_M_key_compare via __is_invocable) is mis-evaluated.  The same
// program verifies with --cpp11 against the same headers, and with gcc 13's
// headers under --cpp20.
#include <map>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::map<int, int> m;
  m[1] = 10;
  __CPROVER_assert(m.size() == 1, "size");
  __CPROVER_assert(m[1] == 10, "value found again");
  __CPROVER_assert(m.count(1) == 1, "count");
  return 0;
}
