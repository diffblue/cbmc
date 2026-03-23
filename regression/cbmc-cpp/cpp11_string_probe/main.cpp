#include <string>
int main()
{
  std::string s = "hello";
  __CPROVER_assert(s.size() == 5, "size");
}
