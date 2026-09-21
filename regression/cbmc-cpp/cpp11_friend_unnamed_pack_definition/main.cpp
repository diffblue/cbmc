extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
template <class T>
struct box
{
  T v;
  template <class Y, class... Args>
  friend box<Y> make(Args &&...);

private:
  box(int, T x) : v(x)
  {
  }
};

template <class T, class... Args>
box<T> make(Args &&...args)
{
  return box<T>(0, args...);
}
} // namespace ns

int main()
{
  ns::box<int> b = ns::make<int>(41);
  __CPROVER_assert(b.v == 41, "friend-declared template definition is called");
  return 0;
}
