// libstdc++ 16's basic_ostream::widen -> ctype<char>::widen ->
// `this->do_widen(__c)' (locale_facets.h line 887): with gcc 16's <locale>
// the virtual call through the facet's vtable pointer is avoided only if
// the modelled "C" locale ctype<char> facet (cpp_typecheck_stdlib.cpp)
// fills the _M_widen cache.  With gcc 11-15 the insertion takes another
// path.
#include <iomanip>
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::stringstream ss;
  ss << std::setw(4) << 7;
  int reached = 1;
  __CPROVER_assert(reached == 1, "setw inserter converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
  return 0;
}
