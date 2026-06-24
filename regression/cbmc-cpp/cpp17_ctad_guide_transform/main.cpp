// N5008 [temp.deduct.guide]: a deduction guide may name a specialization whose
// arguments differ from the constructor argument types.  `Box(T) -> Box<long>`
// always deduces `Box<long>` regardless of the argument type, so the stored
// value has `long` range.
//
// Regression: CBMC ignored the guide and deduced `Box<int>` from the `int`
// argument, truncating the stored value.
template <typename T>
struct Box
{
  T v;
  Box(T x) : v(x) {}
};
template <typename T>
Box(T) -> Box<long>;
int main()
{
  Box b{5};                 // guide forces Box<long>
  b.v = 4000000000L;        // exceeds INT_MAX; fits only in a long member
  __CPROVER_assert(b.v == 4000000000L, "guide forced Box<long>: value not truncated");
  return 0;
}
