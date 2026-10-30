// Decomposition of cpp11_regex_match: CONSTRUCTION of std::regex alone
// (no matching) already exceeds the symex budget by a wide margin
// (>600s; the full test's "solver-time" variance is really symex time
// in the libstdc++ NFA compiler).  Unwind hotspots observed at
// --unwind 5: basic_stringbuf::_M_pbump loops,
// regex_traits::translate_nocase and ctype::tolower recursion.
// Front-end conversion is complete and layout-independent (the
// remaining cost is symbolic execution, not type-checking).
#include <regex>
int main()
{
  std::regex r("hello");
  __CPROVER_assert(true, "regex constructed");
}
