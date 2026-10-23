// N5008 [class.access.general]/5, [expr.type.conv]: in `V{bias, 3}', inside
// a member function of dec, the element `bias' names dec's protected member
// where it appears, which is accessible.  The front end reports "member
// 'dec::bias' is not accessible (protected)" -- the check runs while V's
// constructor body is converted, in V's context.  The declaration form
// `V v{bias, 3}' works.  (CBMC's own smt2_dec.cpp,
// `argv = {solver_binary_or_empty, temp_file_problem()}' with a
// std::vector<std::string>, dog-fooding.)
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
struct V
{
  int f;
  V(std::initializer_list<int> l) : f(*l.begin())
  {
  }
};
struct dec
{
  int run()
  {
    return V{bias, 3}.f;
  }

protected:
  int bias = 10;
};
int main()
{
  dec d;
  __CPROVER_assert(d.run() == 10, "protected member in a braced cast");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
