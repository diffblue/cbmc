// N5008 [over.match.class.deduct] / [dcl.type.class.deduct]: a class template
// name written without a template-argument-list in a prvalue
// (`Box{5}` / `Box(5)`) undergoes class template argument deduction, and the
// surrounding `auto` then deduces the resulting class type.
//
// Regression: CBMC performed CTAD only in the declaration form `Box b{5}`; the
// prvalue feeding `auto` (`auto b = Box{5}`) was not deduced and failed with
// "found no match for symbol 'Box'".
template <typename T>
struct Box
{
  T v;
  Box(T x) : v(x) {}
};
int main()
{
  auto b = Box{5}; // CTAD: Box<int>
  __CPROVER_assert(b.v == 5, "auto = Box{5} deduces Box<int>, value preserved");
  auto c = Box{b.v + 2}; // CTAD: Box<int>
  __CPROVER_assert(c.v == 7, "second CTAD prvalue value preserved");
  return 0;
}
