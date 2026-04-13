// C++17 std::string_view
#include <string_view>
int main()
{
  std::string_view sv = "hello";
  __CPROVER_assert(sv.size() == 5, "string_view size");
  __CPROVER_assert(sv[0] == 'h', "string_view element");
}
