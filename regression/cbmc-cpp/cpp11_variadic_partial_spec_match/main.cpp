// [temp.spec.partial.match] / [temp.class.spec] / [expr.sizeof]/5: a class
// template partial specialization whose pattern is a class-template-id with a
// pack expansion (`primary<Types...>`) must match a concrete instantiation of
// that template, deducing the parameter pack -- for any pack length, including
// zero and one.  CBMC matched the nested template-id arguments positionally and
// never deduced the pack (so the partial specialization was never selected),
// and a single-element pack's `sizeof...` was mis-evaluated as `sizeof(<elem>)`.
// This is the shape of std::tuple_size<std::tuple<Types...>> and many other
// variadic traits.

template <class... Types>
struct primary
{
};

template <class T>
struct count_of; // primary template, intentionally incomplete

template <class... Types>
struct count_of<primary<Types...>>
{
  static const unsigned value = sizeof...(Types);
};

int main()
{
  unsigned zero = count_of<primary<>>::value;
  unsigned one = count_of<primary<int>>::value;
  unsigned two = count_of<primary<int, long>>::value;
  unsigned three = count_of<primary<int, long, char>>::value;

  __CPROVER_assert(zero == 0, "empty pack deduced");
  __CPROVER_assert(one == 1, "pack of 1 deduced");
  __CPROVER_assert(two == 2, "pack of 2 deduced");
  __CPROVER_assert(three == 3, "pack of 3 deduced");
  // Non-vacuity: a wrong value must FAIL, proving the deduced values are
  // genuinely computed and checked (not silently dropped).
  __CPROVER_assert(one == 2, "wrong value FAILs (non-vacuous)");
  return 0;
}
