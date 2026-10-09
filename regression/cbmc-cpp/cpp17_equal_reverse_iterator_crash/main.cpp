// Dog-food kernel (src/util/simplify_expr.cpp:249, the last remaining
// dog-food CRASH): std::equal over rbegin()/rend() with a std::next-
// advanced reverse_iterator makes the front end look up
//   std::vector<T,allocator<T>>::reverse_iterator
// in the namespace during typechecking of the algorithm's
// instantiation, and the symbol was never registered -- the namespacet
// lookup invariant aborts the whole run ("we are assuming that a name
// exists in the namespace").  Plain reverse_iterator loops (rbegin/
// rend and explicit spelling) work; the algorithm + std::next
// combination is required.
#include <algorithm>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::vector<int> a{1, 2, 3};
  std::vector<int> b{9, 2, 3};
  bool suffix_eq = std::equal(a.rbegin(), std::next(a.rbegin(), 2), b.rbegin());
  __CPROVER_assert(suffix_eq, "std::equal over reverse iterators");
  return 0;
}
