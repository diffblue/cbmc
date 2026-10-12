// N5008 [dcl.type.pack.index]/1, [expr.sizeof]/1: `T...[N]' names the N-th
// element of the pack T; sizeof applies to it as to any type-id.  CBMC gets
// `using type = T...[0]' right but evaluates `sizeof(T...[N])' wrongly.
extern "C" void __CPROVER_assert(bool, const char *);

template <class... T>
struct first
{
  using type = T...[0];
};

template <class... T>
constexpr unsigned long size_of_first = sizeof(T...[0]);

template <class... T>
constexpr unsigned long size_of_second = sizeof(T...[1]);

int main()
{
  static_assert(__is_same(first<char, int>::type, char));
  __CPROVER_assert(size_of_first<long, char> == sizeof(long), "first");
  __CPROVER_assert(size_of_second<char, long> == sizeof(long), "second");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
