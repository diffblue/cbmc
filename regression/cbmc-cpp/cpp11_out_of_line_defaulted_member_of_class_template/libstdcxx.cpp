#include <fstream>
#include <string>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::string name = "out.txt";
  auto out = std::ofstream{name};
  int reached = 1;
  __CPROVER_assert(reached == 1, "ofstream constructed");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
}
