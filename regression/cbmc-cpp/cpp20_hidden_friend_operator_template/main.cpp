// N5008 [class.friend]/1 + [namespace.memdef]/3: a friend function
// TEMPLATE defined inside a class is a namespace member found by ADL.
// CBMC discarded such declarations entirely (only friend class
// templates were handled), so the range-adaptor pipe idiom's hidden
// friend operator| never existed and `arr | closure` fell into the
// C-layer arithmetic conversion, silently dropping main (vacuous
// SUCCESS).  Reduced from libc++ <ranges> __range_adaptor_closure.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct closure_t
{
  template <class R>
  int operator()(R &&r)
  {
    return r[0];
  }
  template <class _View, class _Closure>
  friend int operator|(_View &&__view, _Closure __closure)
  {
    return __closure(__view);
  }
};

int main()
{
  int arr[]{3};
  closure_t c{};
  int x = arr | c;
  __CPROVER_assert(x == 3, "pipe through hidden friend");
}
