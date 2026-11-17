// N5008 [temp.variadic]/5, /9: in a member of the partial specialization
// vg<R(A...)>, the function type R(A...) expands the pack A to one
// parameter per element, also when A = {E} is one class type.  libc++'s
// (Xcode 26) std::function constructor forms `__func<_Fp,
// _Rp(_ArgTypes...)>' this way.
extern "C" void __CPROVER_assert(bool, const char *);
template <class F, class S>
class func;
template <class F, class R, class... A>
class func<F, R(A...)>
{
public:
  F f;
};
template <class S>
struct vf;
template <class R, class... A>
struct vf<R(A...)>
{
  unsigned long size = 0;
  template <class F>
  explicit vf(F)
  {
    typedef func<F, R(A...)> Fun;
    size = sizeof(Fun);
  }
};
template <class S>
struct vg;
template <class R, class... A>
struct vg<R(A...)>
{
  unsigned long size = 0;
  vg()
  {
    typedef func<long, R(A...)> Fun;
    size = sizeof(Fun);
  }
};
struct E
{
  int v;
};
int main()
{
  vf<int(E)> h(1L);
  __CPROVER_assert(h.size == sizeof(long), "member template");
  vg<int(E)> g;
  __CPROVER_assert(g.size == sizeof(long), "non-template member");
  __CPROVER_assert(sizeof(func<long, int(E)>) == sizeof(long), "direct");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
