#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
void insert(std::ostringstream &o)
{
  o << "ab";
}
int main()
{
  __CPROVER_assert(true, "converted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
