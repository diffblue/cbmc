#include <string_view>

int main()
{
  std::string_view sv = "hello";
  __CPROVER_assert(sv.size() == 5, "size is 5");
  __CPROVER_assert(sv[0] == 'h', "first char");
  return 0;
}
