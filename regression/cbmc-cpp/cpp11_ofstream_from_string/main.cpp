// C++11 [ofstream.cons]: std::ofstream has a constructor taking a
// const std::string& (filename).  CBMC resolves the construction
// against a wrong candidate and hard-errors with "invalid implicit
// conversion from 'struct basic_string' to 'std::streamsize'"; the
// enclosing function is then silently truncated (vacuous success).
// The shape of `auto out = std::ofstream{outfile}` in
// solver_hardness.cpp/produce_report and goto-harness's doit(),
// which blocks their dog-fooding.
// Note: no assertion on the STREAM's behaviour is made -- writing to
// files is not modeled; the assertion pins that the construction
// CONVERTS and control flow proceeds.
// g++/clang++ accept and verify at runtime.
#include <fstream>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::string name = "out.txt";
  auto out = std::ofstream{name};
  int reached = 1;
  __CPROVER_assert(reached == 1, "ofstream from string converts");
  return 0;
}
