extern "C" void __CPROVER_assert(bool, const char *);
template <class S>
struct G;
// [temp.class.spec.mfunc]/1: members of a partial specialization defined
// out of line; [class.base.init]/1: with their ctor-initializers
template <class R>
struct G<R()>
{
  R x;
  G(R v) : x(v)
  {
  }
  G(const G &);
};
template <class R>
G<R()>::G(const G &o) : x(o.x + 1)
{
}
template <class S>
struct H;
template <class R, class... A>
struct H<R(A...)>
{
  R x;
  H(R v) : x(v)
  {
  }
  H(const H &);
};
template <class R, class... A>
H<R(A...)>::H(const H &o) : x(o.x + 2)
{
}
int main()
{
  G<int()> a(5);
  G<int()> b(a);
  H<int(int, char)> c(5);
  H<int(int, char)> d(c);
  __CPROVER_assert(
    b.x == 6 && d.x == 7, "copy constructors defined out of line");
  __CPROVER_assert(b.x == 5, "WRONG (must FAIL)");
}
