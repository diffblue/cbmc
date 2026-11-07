extern "C" void __CPROVER_assert(bool, const char *);
// the shape of libstdc++'s __atomic_futex_unsigned (atomic_futex.h:155),
// reduced by cvise; the names in namespace std matter, the front end used
// to exclude std::ratio / std::chrono / std::__detail classes from `{}'
namespace std
{
template <long>
struct ratio;
template <typename>
struct duration
{
};
template <unsigned = 0>
struct futex
{
  int calls = 0;
  // [dcl.init.list]/3.5, [over.ics.list]/7: `{}' value-initializes the
  // duration parameter
  void load_and_test_until(duration<ratio<1>>)
  {
    ++calls;
  }
  void load_and_test()
  {
    load_and_test_until({});
  }
};
} // namespace std
int main()
{
  std::futex<> f;
  f.load_and_test();
  __CPROVER_assert(f.calls == 1, "called with an empty braced list");
  __CPROVER_assert(f.calls == 0, "WRONG (must FAIL)");
}
