// C++14 std::chrono basic usage
#include <chrono>
int main()
{
  std::chrono::seconds d(5);
  __CPROVER_assert(d.count() == 5, "seconds");
}
