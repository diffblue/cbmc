// N5008 [temp.friend]/1: `template <typename F> friend int peek(const loc
// &)' introduces the function template peek (no earlier declaration) and
// befriends all its specializations; the definition after the class reads
// the private member.  The front end recorded no friend when the friend
// declaration introduced the template: "member 'loc::impl' is not
// accessible (private)", and peek's body was dropped (the shape of
// libstdc++'s __try_use_facet friend of std::locale; the error shows up
// once the system-header markers are lost, `g++ -E -P').
extern "C" void __CPROVER_assert(bool, const char *);
struct loc
{
  loc() : impl(42)
  {
  }

private:
  int impl;
  // N5008 [temp.friend]/1: every specialization of peek is a friend
  template <typename F>
  friend int peek(const loc &l);
};
template <typename F>
int peek(const loc &l)
{
  return l.impl;
}
int main()
{
  loc l;
  __CPROVER_assert(peek<char>(l) == 42, "friend function template has access");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
