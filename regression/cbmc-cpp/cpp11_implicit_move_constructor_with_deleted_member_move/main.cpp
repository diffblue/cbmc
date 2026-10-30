// N5008 [class.copy.ctor]/10: the defaulted move constructor of H is
// defined as deleted, since M's move constructor is deleted; note 4: it is
// ignored by overload resolution, so H(std::move(a)) uses the copy
// constructor.
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int copies = 0;
struct M
{
  M()
  {
  }
  M(const M &)
  {
    ++copies;
  }
  M(M &&) = delete;
};
struct H
{
  M m;
};
int main()
{
  H a;
  H b(std::move(a));
  __CPROVER_assert(copies == 1, "copy constructor selected");
  __CPROVER_assert(copies == 0, "WRONG (must FAIL)");
}
