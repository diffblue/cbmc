extern "C" void __CPROVER_assert(bool, const char *);
typedef decltype(sizeof(0)) size_t;
namespace ns
{
template <size_t Align>
size_t aligned_size(size_t n)
{
  return (n + Align - 1) / Align * Align;
}
} // namespace ns
template <class T>
struct impl
{
  T value;
  template <class U>
  explicit impl(U &&u) : value(static_cast<U &&>(u))
  {
  }
  // N5008 [class.pre]/2, [temp.local]/1: the injected-class-name names the
  // class (here as a type-id of alignof and sizeof), not its constructors
  size_t storage() const
  {
    return ::ns::aligned_size<alignof(impl)>(sizeof(impl));
  }
};
int main()
{
  impl<int> i(3);
  __CPROVER_assert(i.storage() == sizeof(int), "injected-class-name");
  __CPROVER_assert(i.storage() == 0, "WRONG (must FAIL)");
  return 0;
}
