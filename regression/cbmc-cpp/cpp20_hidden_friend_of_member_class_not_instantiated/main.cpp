// N5008 [temp.inst]/4: instantiating a class template specialization
// instantiates the declarations, not the definitions, of the friend
// functions defined in it -- also in its member classes.  The definition of
// view<int, unreachable>::sentinel's `operator-', ill-formed for that
// specialization, was instantiated (and dropped) although nothing uses it
// (libc++'s iota_view<int, unreachable_sentinel_t>::__sentinel).
extern "C" void __CPROVER_assert(bool, const char *);

struct unreachable
{
};

template <class S, class B>
struct view
{
  struct iterator
  {
    S value;
  };
  struct sentinel
  {
    B bound = B();
    sentinel() = default;
    explicit sentinel(B b) : bound(b)
    {
    }
    friend int operator-(const iterator &x, const sentinel &y)
    {
      return x.value - y.bound;
    }
  };
  S start;
  B bound;
};

int main()
{
  view<int, unreachable> v{1, {}};
  view<int, int>::iterator i{1};
  view<int, int>::sentinel e{4};
  __CPROVER_assert(i - e == -3, "the friend of view<int, int>");
  __CPROVER_assert(v.start == 1, "view<int, unreachable>");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
