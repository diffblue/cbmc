// N5008 [stmt.ambig]/1: a statement that can syntactically be a declaration
// is one; `set(o);' can only be a declaration if `set' names a TYPE, and a
// class template name without template arguments is not a type-name
// ([temp.names], [dcl.type.simple]).  So in a constructor body it calls
// the member function `set' -- declared later in the class, visible in the
// body ([class.mem.general]/7) -- even with std::set in scope.  The parser
// took the template name for a type and declared a variable `o' ("found no
// match for symbol 'set'"; CBMC's own object_factory_parameterst with
// <set> included, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
template <class T>
struct set
{
  T x;
};
int set2(int)
{
  return 0;
}
} // namespace ns
using namespace ns;
struct params
{
  explicit params(int o)
  {
    set(o);
  }
  int n = 0;
  void set(int o);
};
void params::set(int o)
{
  n = o * 2;
}
struct params2
{
  explicit params2(int o)
  {
    set2(o);
  }
  int n = 0;
  void set2(int o)
  {
    n = o * 3;
  }
};
int main()
{
  params p(4);
  __CPROVER_assert(p.n == 8, "member hides class template of a used namespace");
  params2 q(4);
  __CPROVER_assert(q.n == 12, "member hides function of a used namespace");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
