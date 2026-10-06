// N5008 [temp.inst]/1-3, [dcl.fct]/12: a member function declaration does
// not require its return type to be complete, so ios<char>'s
// `ostream<char> *set_rdbuf(...)' does not instantiate ostream<char> while
// ios<char> -- a base of ostream<char> -- is being instantiated (the
// libstdc++ basic_ios / basic_ostream / basic_ofstream shape)
extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct ostream;
struct streambuf
{
  int k = 4;
};
template <class T>
struct ios
{
  streambuf *buf = nullptr;
  ostream<char> *set_rdbuf(streambuf *b)
  {
    buf = b;
    return nullptr;
  }
};
template <class C>
struct ostream : virtual ios<C>
{
};
template <class C>
struct ofstream : ostream<char>
{
  streambuf fb;
  ofstream()
  {
    ostream::set_rdbuf(&fb);
  }
};
template <class C>
struct istream : ios<C>
{
  istream &ignore(long);
};
template <>
istream<char> &istream<char>::ignore(long);
int main()
{
  ofstream<char> o;
  __CPROVER_assert(o.buf == &o.fb, "member of the virtual base");
  __CPROVER_assert(o.buf == nullptr, "WRONG (must FAIL)");
}
