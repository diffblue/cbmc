// N5008 [temp.deduct.call]/2: array-to-pointer decay applies only when
// the function parameter is NOT a reference type.  For the deduction
// guide `holder(R&&) -> holder<all_t<R>>`, the argument `arr` (an
// lvalue of type int[3]) must deduce R = int(&)[3]; the alias then
// preserves the reference-to-array, so CTAD yields holder<int(&)[3]>.
// CBMC decays the array to a pointer during class template argument
// deduction, CTAD fails ("invalid implicit conversion from 'signed int
// [3]' to 'struct holder'"), and main is silently dropped.
// This is the ranges pipe's current blocker: libc++'s
//   take_view(_Range&&, ...) -> take_view<views::all_t<_Range>>
// must produce take_view<int(&)[1]>, but CBMC produces
// take_view<int*>, and downstream iterator_t<int*> has no viable
// begin() ([range.take]).
// g++ and clang++ both accept (-Werror) and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> T __declval(int);
template <class T> decltype(__declval<T>(0)) declval();
struct
{
  template <class T, int N> int operator()(T (&)[N])
  {
    return N;
  }
} arr_size;
template <class R> using all_t = decltype(declval<R>());
template <class V> struct holder
{
  V base_;
  int size()
  {
    return arr_size(base_);
  }
};
template <class R> holder(R &&) -> holder<all_t<R>>;
int main()
{
  int arr[3]{1, 2, 3};
  holder h(arr);
  __CPROVER_assert(h.size() == 3, "deduction guide preserves array reference");
  return 0;
}
