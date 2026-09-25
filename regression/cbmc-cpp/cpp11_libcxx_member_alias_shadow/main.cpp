// Distilled from libc++'s <vector> (__split_buffer): a class
// template's member alias `iterator` -- defined through a typedef
// chain -- fails to resolve ("found no match for symbol 'iterator'")
// when a same-named class template is forward-declared at namespace
// scope (libc++'s deprecated std::iterator) AND CBMC runs in libc++
// mode (--stdlib libc++; the clang parser flavor).  [basic.scope.scope],
// [class.member.lookup]: the member alias declaration hides the
// namespace-scope name inside the class.  Plain (gcc-flavor) mode
// resolves fine; removing the namespace-scope forward declaration
// resolves fine; the namespace need not be `std`.  The diagnostic is
// currently emitted but swallowed (the run still reports
// VERIFICATION SUCCESSFUL), so this desc forbids the diagnostic
// text.  Root cause of the nine cpp11/17 *_libcxx vector-family
// failures.
extern "C" void __CPROVER_assert(bool, const char *);

namespace std
{
template <class>
struct iterator;

struct allocator_traits
{
  typedef int pointer;
};

template <class>
struct __split_buffer
{
  typedef allocator_traits __alloc_traits;
  using iterator = __alloc_traits::pointer;
  iterator end;
};

template <class>
struct vector
{
  void push_back(int)
  {
  }
  void __swap_out_circular_buffer(__split_buffer<int>);
};
} // namespace std

int main()
{
  std::vector<int> v;
  v.push_back(42);
  __CPROVER_assert(true, "class with shadowed member alias converts");
  return 0;
}
