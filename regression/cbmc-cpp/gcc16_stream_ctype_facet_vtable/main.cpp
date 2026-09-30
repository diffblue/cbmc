// libstdc++ 16's basic_ostream::widen -> ctype<char>::widen ->
// `this->do_widen(__c)' (locale_facets.h line 887): the virtual call goes
// through the facet's vtable pointer, which the front end's model of the
// ctype facet (cpp_typecheck_stdlib.cpp: use_facet/has_facet overrides)
// leaves invalid for gcc 16's <locale> ("pointer outside object bounds in
// ((struct virtual_table::ctype *)this->facet@vtable_pointer)->do_widen").
// With gcc 11-15 the same insertion verifies.
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
