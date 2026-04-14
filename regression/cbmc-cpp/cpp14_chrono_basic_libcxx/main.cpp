// C++14 std::chrono basic usage
#include <chrono>
int main()
{
  std::chrono::seconds d;
  __CPROVER_assert(sizeof(d) > 0, "duration exists");
}
