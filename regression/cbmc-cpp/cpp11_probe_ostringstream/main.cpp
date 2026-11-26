// N5008 [ostringstream], [ostream.inserters.arithmetic]: inserting an int into
// a std::ostringstream.
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::ostringstream os;
  os << 42;
  __CPROVER_assert(os.str() == "42", "integer insertion");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
