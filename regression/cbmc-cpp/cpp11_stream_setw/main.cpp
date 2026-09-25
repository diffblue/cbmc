// C++11 [ext.manip]/[iomanip]: `os << std::setw(n)` inserts the
// smanip returned by setw via the operator<< overload taking the
// manipulator.  CBMC used to fail to resolve the inserter
// ("operator 'shl' not defined") because [temp.deduct.call]/4.3
// deduction only inspected DIRECT bases -- basic_stringstream derives
// from basic_ostream only through basic_iostream.  Fixed 2026-07-21
// (transitive base walk).  First error of solver_hardness.cpp's
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
