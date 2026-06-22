// [temp.spec.partial.match] / [temp.class.spec]: a class template partial
// specialization whose pattern is a class-template-id with a pack expansion
// (`primary<Types...>`) must match a concrete instantiation of that template,
// deducing the parameter pack.  CBMC matched the nested template-id arguments
// positionally and never deduced the pack, so such a partial specialization was
// never selected (the incomplete primary template was used and the member
// accesses were silently dropped).  This is the shape of
// std::tuple_size<std::tuple<Types...>> and many other variadic traits.

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
  unsigned two = count_of<primary<int, long>>::value;
  unsigned three = count_of<primary<int, long, char>>::value;

  __CPROVER_assert(two == 2, "pack of 2 deduced");
  __CPROVER_assert(three == 3, "pack of 3 deduced");
  // Non-vacuity: a wrong value must FAIL, proving the deduced value is
  // genuinely computed and checked (not silently dropped).
  __CPROVER_assert(two == 99, "wrong value FAILs (non-vacuous)");
  return 0;
}
