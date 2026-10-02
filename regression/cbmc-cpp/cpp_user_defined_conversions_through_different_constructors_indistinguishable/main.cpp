extern "C" void __CPROVER_assert(bool, const char *);
namespace s
{
template <class P>
struct holder
{
  P p;
  void dispose()
  {
    delete p;
  }
};
// [over.match.best]/2.1, [over.ics.rank]/3.3: `o == 0' selects
// operator==(ord, unspec).  The hidden friend operator==(count, count) is
// not even a candidate ([basic.lookup.argdep]/4.3: count is not an
// associated class of ord or int); the front end considered it and, ranking
// the conversion 0 -> unspec through unspec(unspec *) worse than the
// unrelated 0 -> count through count(P), selected it.  Its constructor
// template count(P) must not be odr-used: [temp.inst]/11 would make
// holder<ord>::dispose ill-formed (libstdc++'s __shared_count(_Ptr) and
// _Sp_counted_ptr<_Ptr>::_M_dispose, considered for `partial_ordering != 0')
struct count
{
  template <class P>
  count(P)
  {
    (new holder<P>)->dispose();
  }
  friend bool operator==(count, count)
  {
    return false;
  }
};
struct unspec
{
  unspec(unspec *)
  {
  }
};
struct ord
{
};
bool operator==(ord, unspec)
{
  return true;
}
} // namespace s
int main()
{
  s::ord o;
  __CPROVER_assert(o == 0, "equal");
  __CPROVER_assert(!(o == 0), "WRONG (must FAIL)");
}
