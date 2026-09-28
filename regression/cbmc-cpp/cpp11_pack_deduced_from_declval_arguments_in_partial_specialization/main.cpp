#include <new>
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&declval();
struct true_type
{
  static constexpr bool value = true;
};
struct false_type
{
  static constexpr bool value = false;
};
struct path
{
  int n;
};
// constructible only from two paths
struct storage
{
  int sum;
  storage(const path &a, const path &b) : sum(a.n + b.n)
  {
  }
};
template <class T>
struct alloc
{
  template <class U, class... Args>
  void construct(U *p, Args &&...args)
  {
    ::new((void *)p) U(static_cast<Args &&>(args)...);
  }
};
// libc++'s __has_construct: the partial specialization's first argument
// is the type of the call `declval<A>().construct(declval<Args>()...)',
// with a PACK of call arguments; U is deduced from the first one and the
// member template's pack Args from the rest ([temp.deduct.call]/1)
template <class, class A, class... Args>
struct has_construct_impl : false_type
{
};
template <class A, class... Args>
struct has_construct_impl<
  decltype((void)declval<A>().construct(declval<Args>()...)),
  A,
  Args...> : true_type
{
};
template <class A, class... Args>
struct has_construct : has_construct_impl<void, A, Args...>
{
};
int main()
{
  alignas(storage) unsigned char buffer[sizeof(storage)];
  alloc<storage> a;
  path p{1}, q{2};
  a.construct(reinterpret_cast<storage *>(buffer), p, q);
  __CPROVER_assert(
    reinterpret_cast<storage *>(buffer)->sum == 3,
    "constructed from two paths");
  __CPROVER_assert(
    has_construct<alloc<storage>, storage *, path, path>::value,
    "construct(storage *, path, path) is valid");
  __CPROVER_assert(
    !has_construct<alloc<storage>, storage *, path, path>::value,
    "WRONG (must FAIL)");
}
