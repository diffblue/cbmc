extern "C" void __CPROVER_assert(bool, const char *);
#include <vector>
template <class A, class B, bool same_size> struct zip_iteratort { A a; B b; };
template <class It> struct ranget
{
  It b, e;
  It begin() const { return b; }
  It end() const { return e; }
  template <bool same_size = true, class other_iteratort>
  ranget<zip_iteratort<It, other_iteratort, same_size>> zip(ranget<other_iteratort> other)
  {
    return ranget<zip_iteratort<It, other_iteratort, same_size>>{{b, other.b}, {e, other.e}};
  }
  template <bool same_size = true, class containert>
  auto zip(containert &container)
    -> ranget<zip_iteratort<It, decltype(container.begin()), same_size>>
  {
    return zip<same_size>(ranget<decltype(container.begin())>{container.begin(), container.end()});
  }
};
int main()
{
  std::vector<int> v{1, 2, 3};
  int arr[3] = {4, 5, 6};
  ranget<int *> r{arr, arr + 3};
  auto z = r.zip(v);
  __CPROVER_assert(*z.b.a == 4 && *z.b.b == 1, "zip over a container: inner call with an rvalue ranget picks the by-value overload");
  return 0;
}
