extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct stream
{
  int state;
  // declared in the class template, defined outside it ([temp.mem.class])
  class sentry;
  int tellp();
};
template <class C>
class stream<C>::sentry
{
  bool ok;

public:
  explicit sentry(stream<C> &s) : ok(s.state == 0)
  {
  }
  explicit operator bool() const
  {
    return ok;
  }
};
template <class C>
int stream<C>::tellp()
{
  sentry cerb(*this);
  if(cerb)
    return 2;
  return -1;
}
int main()
{
  stream<char> s{0};
  __CPROVER_assert(s.tellp() == 2, "sentry constructed and tested");
  stream<char> f{1};
  __CPROVER_assert(f.tellp() == -1, "failed stream");
  __CPROVER_assert(s.tellp() == -1, "WRONG (must FAIL)");
}
