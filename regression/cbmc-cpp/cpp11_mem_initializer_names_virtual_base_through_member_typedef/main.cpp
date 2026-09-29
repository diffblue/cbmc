extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct ios
{
  int state = 1;
  ios() = default;
  void move(ios &o)
  {
    state = o.state;
  }
};
template <class C>
struct ostream : virtual ios<C>
{
  typedef ios<C> ios_type;
  ostream()
  {
  }
  // libstdc++'s basic_ostream move constructor: the virtual base is named in
  // the mem-initializer through a member typedef ([class.base.init]/2)
  ostream(ostream &&r) : ios_type()
  {
    ios_type::move(r);
  }
};
int main()
{
  ostream<char> a;
  a.state = 5;
  ostream<char> b(static_cast<ostream<char> &&>(a));
  __CPROVER_assert(b.state == 5, "moved through the typedef");
  __CPROVER_assert(b.state == 1, "WRONG (must FAIL)");
}
