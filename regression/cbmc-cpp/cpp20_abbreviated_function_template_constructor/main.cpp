extern "C" void __CPROVER_assert(bool, const char *);
template <class It, class Sent = It>
struct sub
{
  It b;
  Sent e;
  // N5008 [dcl.fct]/22: an abbreviated function template constructor;
  // {first, last} initializes the parameter sub&& through it
  // ([dcl.init.list]/3.7, [over.ics.list])
  sub(auto first, Sent last) : b(first), e(last)
  {
  }
};
template <class V>
struct view
{
  V base;
  view(V &&v) : base(static_cast<V &&>(v))
  {
  }
};
int main()
{
  const char s[] = "ab";
  const char *first = s, *last = s + 2;
  view<sub<const char *>> v({first, last});
  __CPROVER_assert(v.base.e - v.base.b == 2, "braced argument");
  __CPROVER_assert(v.base.e == v.base.b, "WRONG (must FAIL)");
  return 0;
}
