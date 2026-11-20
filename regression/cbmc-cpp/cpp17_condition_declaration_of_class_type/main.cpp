// N5008 [stmt.pre]/4-6: a condition may be a declaration; the declared
// object is contextually converted to bool and its lifetime extends over the
// substatements.  For an object of class type (an optional, destroyed at the
// end of the statement) the typechecked declaration block also holds the
// constructor call; the front end asserted that it holds exactly one
// statement (CBMC's own local_safe_pointers.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <optional>
struct S
{
  int v;
  S(int x) : v(x)
  {
  }
  ~S()
  {
  }
};
std::optional<S> get(bool b)
{
  if(b)
    return S{5};
  return {};
}
int main()
{
  int n = 0;
  if(auto r = get(true))
    n += r->v;
  if(auto r = get(false))
    n += 100;
  else
    n += 1;
  if(std::optional<int> q = std::optional<int>{3})
    n += *q;
  int k = 2;
  while(std::optional<S> w = get(k > 0))
  {
    n += w->v;
    --k;
  }
  __CPROVER_assert(n == 19, "condition declarations of class type");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
