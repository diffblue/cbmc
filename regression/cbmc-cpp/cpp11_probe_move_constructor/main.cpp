// N5008 [class.copy.ctor], [utility.syn]: std::move selects the move
// constructor.
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int *p;
  S(int *q) : p(q)
  {
  }
  S(S &&o) : p(o.p)
  {
    o.p = nullptr;
  }
};
int main()
{
  int v = 1;
  S a(&v);
  S b(std::move(a));
  __CPROVER_assert(a.p == nullptr && b.p == &v, "move constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
