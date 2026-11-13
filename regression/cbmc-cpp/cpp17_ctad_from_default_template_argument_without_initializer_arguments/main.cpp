extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [over.match.class.deduct]/1.2, [temp.deduct.general]/5: `less{}'
// deduces less<void> from the default template argument (the MSVC STL's
// <charconv> _Floating_to_chars_general_precision)
namespace s
{
template <class T = void>
struct less
{
  bool operator()(const T &a, const T &b) const
  {
    return a < b;
  }
};
template <>
struct less<void>
{
  template <class A, class B>
  bool operator()(const A &a, const B &b) const
  {
    return a < b;
  }
};
template <class It, class V, class P>
It lower(It f, It l, const V &v, P p)
{
  for(; f != l; ++f)
    if(!p(*f, v))
      return f;
  return l;
}
template <class T>
int find(const T *b, const T *e, T v)
{
  const T *r = [=]
  {
    if constexpr(sizeof(T) > 1)
    {
      if(v > 1)
        return s::lower(b, e, v, less{});
    }
    return b;
  }();
  return r - b;
}
} // namespace s
int main()
{
  const unsigned t[] = {1, 3, 5, 7};
  __CPROVER_assert(s::find(t, t + 4, 5u) == 2, "less{}");
  __CPROVER_assert(s::find(t, t + 4, 5u) == 3, "WRONG (must FAIL)");
}
