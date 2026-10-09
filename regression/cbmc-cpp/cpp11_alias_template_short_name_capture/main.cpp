extern "C" void __CPROVER_assert(bool, const char *);
template <bool>
struct _IfImpl
{
  static const int tag = 1;
};
template <bool _Cond, class, class>
using _If = _IfImpl<_Cond>;
template <bool _Bp, class _ElseRes>
struct conditional
{
  using type = _If<_Bp, int, _ElseRes>;
};
template <bool _Bp, class _If, class _Then>
using __conditional_t = typename conditional<_Bp, _Then>::type;
template <class _Tp>
struct vec
{
  using __reloc = __conditional_t<true, vec, void>;
  int go()
  {
    return __reloc::tag;
  }
};
int main()
{
  vec<int> v;
  __CPROVER_assert(v.go() == 1, "in-progress class as conditional argument");
  return 0;
}
