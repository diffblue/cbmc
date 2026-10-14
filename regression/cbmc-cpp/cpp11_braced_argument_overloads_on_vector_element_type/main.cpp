// N5008 [over.ics.list]/7, [over.match.list]/1: a braced-init-list
// converts to std::vector<X> through the initializer-list constructor only
// when every element converts to X, and otherwise through a constructor
// taking the elements as arguments.  `pick({r})' with an E lvalue r and
// overloads for std::vector<E> and std::vector<S> -- S not constructible
// from an E -- has only the first candidate viable.  The front end took
// the initializer-list constructor of vector<S> for viable without checking
// the element, and a single element for a possible argument of the
// iterator-pair constructor template: "symbol 'pick' does not uniquely
// resolve" (CBMC's own propagate.cpp, lambda_exprt::instantiate({e}),
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <vector>
struct E
{
  int v;
};
struct S : E
{
  explicit S(int x) : E{x}
  {
  }
};
int pick(const std::vector<E> &)
{
  return 1;
}
int pick(const std::vector<S> &)
{
  return 2;
}
int main()
{
  E e{3};
  E &r = e;
  S s(4);
  __CPROVER_assert(pick({r}) == 1, "E element: only vector<E> is viable");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
