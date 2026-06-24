// N5008 [over.match.class.deduct]/1 copy deduction candidate: when a class
// template is initialised from a single object that is already a
// specialization of that template, deduction selects that same specialization.
// `Box c{b}` with `b` of type `Box<int>` is `Box<int>` (a copy), not
// `Box<Box<int>>`.
//
// Regression: CBMC mapped the argument's type positionally onto the template
// parameter, deducing the nested `Box<Box<int>>` and then failing with
// "no body for callee Box<Box<int>>::Box(...)".
template <typename T>
struct Box
{
  T v;
  Box(T x) : v(x) {}
};
int main()
{
  int n; // nondet
  Box b{n};            // Box<int>
  Box c{b};            // copy deduction: Box<int>
  __CPROVER_assert(c.v == n, "copy-deduced Box<int> preserves the value");
  return 0;
}
