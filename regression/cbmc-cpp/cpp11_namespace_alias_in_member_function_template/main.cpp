extern "C" void __CPROVER_assert(bool, const char *);

namespace detail
{
namespace impl
{
template <int N>
int get(int x)
{
  return x + N;
}
} // namespace impl
} // namespace detail

namespace impl
{
int twice(int x)
{
  return 2 * x;
}
} // namespace impl

// [namespace.alias]/2: a namespace alias declared in the body of a member
// function template of a class template (libstdc++'s variant::emplace,
// `namespace __variant = std::__detail::__variant;')
template <typename T>
struct box
{
  T value;
  template <int N>
  int add() const
  {
    namespace alias = detail::impl;
    return alias::get<N>(value);
  }
  int doubled() const
  {
    // the namespace-name is looked up where the alias is declared, which
    // finds the namespace, not the alias
    namespace impl = impl;
    return impl::twice(value);
  }
};

int main()
{
  box<int> b{5};
  __CPROVER_assert(b.add<3>() == 8, "alias in a member function template");
  __CPROVER_assert(b.doubled() == 10, "alias of the same name");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
