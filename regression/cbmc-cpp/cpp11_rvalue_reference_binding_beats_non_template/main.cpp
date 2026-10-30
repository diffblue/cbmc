extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [over.match.best]/2.1, [over.ics.rank]/3.2.3: binding an rvalue
// reference to an rvalue is better than binding an lvalue reference; this
// decides before the preference for a non-template ([over.match.best]/2.4)
struct up
{
  int which = 0;
  up() = default;
  up(up &&) = default;
  template <class D = int, int = 0>
  up &operator=(up &&)
  {
    which = 2;
    return *this;
  }
  up &operator=(const up &) = delete;
};
int main()
{
  up p;
  p = up();
  __CPROVER_assert(p.which == 2, "move assignment template");
  __CPROVER_assert(p.which == 0, "WRONG (must FAIL)");
  return 0;
}
