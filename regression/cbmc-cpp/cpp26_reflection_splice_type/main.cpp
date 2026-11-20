// P2996R13 [expr.reflect], [dcl.type.splice] (C++26 static reflection,
// adopted after N5008): the spliced type is int.
extern "C" void __CPROVER_assert(bool, const char *);
constexpr auto r = ^^int;
using T = [:r:];
int main()
{
  T x = 4;
  __CPROVER_assert(
    sizeof(T) == sizeof(int) && x == 4, "the spliced type is int");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
