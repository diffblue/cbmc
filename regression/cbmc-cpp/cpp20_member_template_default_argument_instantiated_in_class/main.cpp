// N5008 [temp.inst]/12 ([dcl.fct.default]/5): a default argument of a member
// function template of a class template specialization is substituted in
// the context of the specialization.  libstdc++ 13's basic_string(const
// _CharT *, const _Alloc & = _Alloc()) is a constructor template in C++20.
// Instantiated while std::map<std::string, int> was being defined, its
// default argument was kept for later as if declared in that class, in a
// scope that did not survive the instantiation: `std::string("h")' then
// failed with "symbol '_Alloc' is unknown".
#include <map>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
std::map<std::string, int> m;
int main()
{
  std::string s = std::string("h");
  __CPROVER_assert(s.size() == 1, "constructed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
