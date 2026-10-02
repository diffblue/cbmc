extern "C" void __CPROVER_assert(bool, const char *);
// [over.match.class.deduct]/5, [over.match.copy]/1.1, [over.match.viable]/2.3:
// in copy-initialization the guide from the explicit constructor is not a
// candidate; the one from the converting constructor, viable through its
// default arguments, deduces G<int> (direct-initialization `G d(1);' would
// be ambiguous)
template <class T>
struct G
{
  T v;
  explicit G(T t) : v(t)
  {
  }
  G(T, int = 0, int = 0) : v(2)
  {
  }
};
int main()
{
  G g = 1;
  __CPROVER_assert(g.v == 2, "converting constructor");
  __CPROVER_assert(g.v != 2, "WRONG (must FAIL)");
}
