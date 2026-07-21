// C++11 [ext.manip]/[iomanip]: `os << std::setw(n)` inserts the
// smanip returned by setw via the operator<< overload taking the
// manipulator.  CBMC fails to resolve the inserter for std::_Setw
// ("operator 'shl' not defined for types 'struct basic_stringstream'
// and 'struct std::_Setw'", surfaced through the _Require SFINAE
// chain in <ostream>), and the enclosing function is silently
// truncated.  First error of solver_hardness.cpp's
// goto_instruction2string and the likely root of the downstream
// with_solver_hardness signature collapse.
// g++/clang++ accept and verify at runtime.
#include <iomanip>
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::stringstream ss;
  ss << std::setw(4) << 7;
  int reached = 1;
  __CPROVER_assert(reached == 1, "setw inserter converts");
  return 0;
}
