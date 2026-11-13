// P2996R13 [meta.reflection] (C++26 static reflection, adopted after N5008):
// S has two data members.
#include <meta>
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int a;
  double b;
};
int main()
{
  constexpr auto members =
    std::define_static_array(std::meta::nonstatic_data_members_of(
      ^^S, std::meta::access_context::unchecked()));
  __CPROVER_assert(members.size() == 2, "S has two data members");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
