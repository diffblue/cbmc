// N5008 [dcl.spec.auto.general]/13 + [over.match.best]: a
// declared-but-never-defined `auto` overload must not outrank the
// defined, more-specialized array-reference overload -- the shape of
// libc++'s ranges `end` niebloid (`end(T (&)[N])` with an `end(T)`
// SFINAE sibling).  Selecting the bodiless generic left its
// undeduced placeholder in the caller ("conversion from
// '<<type:auto>>'"), the first conversion blocker of the whole cpp20
// libc++ family.
extern "C" void __CPROVER_assert(bool, const char *);
struct
{
  template <class T, int N> auto operator()(T (&t)[N])
  {
    return t;
  }
  template <class T> auto operator()(T);
} end_fn;
int main()
{
  unsigned arr[]{0, 1, 2};
  unsigned *p = end_fn(arr);
  __CPROVER_assert(p == arr, "decayed pointer");
  return 0;
}
