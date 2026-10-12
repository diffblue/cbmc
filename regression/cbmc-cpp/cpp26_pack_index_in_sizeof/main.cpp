// N5008 [dcl.type.pack.index]/1, [expr.sizeof]/1: `T...[N]' names the N-th
// element of the pack T; sizeof applies to it as to any type-id.  The parser
// read it as an array of T with bound N, which only some substitution paths
// recognized: `sizeof(T...[N])' in a variable template was sizeof(T[N]).
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

template <class... T>
unsigned long size_of_last()
{
  return sizeof(T...[sizeof...(T) - 1]);
}

template <class T>
constexpr unsigned long array_size = sizeof(T[3]);

int main()
{
  static_assert(__is_same(first<char, int>::type, char));
  __CPROVER_assert(size_of_first<long, char> == sizeof(long), "first");
  __CPROVER_assert(size_of_second<char, long> == sizeof(long), "second");
  __CPROVER_assert(size_of_last<char, short, long>() == sizeof(long), "last");
  __CPROVER_assert(array_size<int> == 3 * sizeof(int), "an array is no pack");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
