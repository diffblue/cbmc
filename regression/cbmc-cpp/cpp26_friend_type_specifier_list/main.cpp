// N5008 [class.friend]/3: a friend-type-declaration may list several
// friend-type-specifiers, and each may be a pack expansion; an element that
// does not designate a class type (int below) is ignored.
extern "C" void __CPROVER_assert(bool, const char *);
struct C;
template <class... Ts>
class R
{
  friend C, Ts...;
  int v = 4;
};
struct A
{
  static int get(const R<A, int, struct B> &r)
  {
    return r.v;
  }
};
struct B
{
  static int get(const R<A, int, B> &r)
  {
    return r.v + 1;
  }
};
struct C
{
  static int get(const R<> &r)
  {
    return r.v + 2;
  }
};
int main()
{
  R<A, int, B> r;
  R<> e;
  __CPROVER_assert(
    A::get(r) == 4 && B::get(r) == 5 && C::get(e) == 6, "friends");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
