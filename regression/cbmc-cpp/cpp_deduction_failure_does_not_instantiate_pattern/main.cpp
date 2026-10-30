extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct tr
{
  static C *copy(C *d, const C *s)
  {
    *d = *s;
    return d;
  }
};
template <class C, class T>
struct sb
{
  C buf[2];
  virtual void put(const C *s)
  {
    T::copy(buf, s);
  }
  virtual ~sb()
  {
  }
};
template <class C, class T>
struct os
{
  sb<C, T> b;
};
template <class C>
struct oss : os<C, tr<C>>
{
};
template <class T>
int operator<<(os<char, T> &, const char *)
{
  return 1;
}
// [temp.deduct.call]/4-5, [temp.deduct.type]/1: os<wchar_t, T> does not
// match oss<char> or its base os<char, tr<char>> (wchar_t is not char), so
// deduction fails; nothing requires os<wchar_t, tr<char>> to be complete
// ([temp.inst]/2), and its instantiation -- with sb<wchar_t, tr<char>>,
// whose put is ill-formed -- must not happen (libc++'s deleted
// `operator<<(basic_ostream<wchar_t, _Traits> &, char16_t)' considered for
// `ostringstream << "ab"')
template <class T>
int operator<<(os<wchar_t, T> &, char16_t) = delete;
int main()
{
  oss<char> o;
  __CPROVER_assert((o << "ab") == 1, "char inserter");
  __CPROVER_assert((o << "ab") != 1, "WRONG (must FAIL)");
}
