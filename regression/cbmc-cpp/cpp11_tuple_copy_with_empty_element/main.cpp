// N5008 [class.copy.ctor]/14, [tuple.cnstr]/12: copying a tuple copies its
// elements; an empty element is copied as a class object with no
// subobjects.  libstdc++ stores it in a [[no_unique_address]] member of an
// empty base, which has zero size and may be laid out at the end of the
// tuple; reading the source element's byte went past the end of its object.
#include <tuple>
extern "C" void __CPROVER_assert(bool, const char *);

struct P
{
};

int main()
{
  P p;
  std::tuple<P, int> t(p, 10);
  std::tuple<P, int> u(t);
  u = t;
  __CPROVER_assert(std::get<1>(u) == 10, "copied");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
