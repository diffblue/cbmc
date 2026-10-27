// N5008 [class.access.general]/6: access to a name is checked in the context
// in which the name appears.  The elements of a braced-init-list argument
// `And a({this->expr})' are expressions of the calling member function,
// where the private member is accessible.  When the braced list went to an
// initializer_list constructor (std::vector<E>), the elements were
// typechecked again while the constructor was resolved -- in the callee
// class's scope -- and the member was "not accessible (private)" (CBMC's
// own guard_exprt::add, dog-fooding).  Also [dcl.init.list]/5: the backing
// array of an initializer_list whose elements are not constants is filled
// where the list is evaluated; it was a static initializer reading the
// local `e' before it existed (all the elements read as zero).
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
#include <vector>
struct E
{
  int v;
};
struct And
{
  std::vector<E> ops;
  explicit And(std::vector<E> o) : ops(o)
  {
  }
};
class G
{
public:
  void add(const E &e)
  {
    if(this->expr.v != 7)
    {
      And a({this->expr}); // braced-init-list of a private member of *this
      this->expr = a.ops[0];
    }
    expr.v += e.v;
  }
  int get() const
  {
    return expr.v;
  }

private:
  E expr{1};
};
int main()
{
  G g;
  g.add(E{2});
  __CPROVER_assert(g.get() == 3, "private member in braced-init-list argument");
  E e{4};
  std::vector<E> v({e, E{5}});
  __CPROVER_assert(
    v.size() == 2 && v[0].v == 4 && v[1].v == 5, "local in braced list");
  std::initializer_list<E> l{e};
  __CPROVER_assert(l.begin()->v == 4, "initializer_list of a local");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
