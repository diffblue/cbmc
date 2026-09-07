// Dog-food kernel (src/util/range.h zip): two member function
// templates, one taking ranget<OtherIt> and one taking containert&
// (both with a leading defaulted non-type parameter), called with a
// ranget argument: [over.match.best]/[temp.func.order] partial
// ordering must prefer the ranget overload; CBMC reports
// "symbol 'zip' does not uniquely resolve".
extern "C" void __CPROVER_assert(bool, const char *);
template <class It> struct ranget
{
  It b_, e_;
  It begin()
  {
    return b_;
  }
  It end()
  {
    return e_;
  }
  template <bool same_size = true, class OtherIt>
  int zip(ranget<OtherIt> other)
  {
    return *begin() + *other.begin();
  }
  template <bool same_size = true, class containert>
  auto zip(containert &container)
    -> decltype(container.begin(), 0)
  {
    ranget<decltype(container.begin())> r{container.begin(), container.end()};
    return zip<same_size>(r);
  }
};
int main()
{
  int a[2] = {1, 2}, b[2] = {30, 40};
  ranget<int *> ra{a, a + 2};
  ranget<int *> rb{b, b + 2};
  __CPROVER_assert(ra.zip(rb) == 31, "zip overloads resolve");
  return 0;
}
