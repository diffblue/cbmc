// N5008 [over.match.class.deduct]: class template argument deduction for a
// functional-notation expression `C(args)` naming a class template without a
// template-argument-list -- e.g. `std::optional(x)` -- deduces the class
// template arguments (via a deduction guide) rather than being a function call.
// CBMC parsed `C(args)` as a function call and reported "found no match for C".

extern "C" void __CPROVER_assert(int, const char *);

template <typename T>
struct Box
{
  T v;
  Box(T x) : v(x) {}
};
template <typename T>
Box(T) -> Box<T>;

int main()
{
  auto b = Box(42); // CTAD -> Box<int>
  __CPROVER_assert(b.v == 42, "CTAD deduced Box<int>");
  __CPROVER_assert(b.v != 42, "WRONG must FAIL");
  return 0;
}
