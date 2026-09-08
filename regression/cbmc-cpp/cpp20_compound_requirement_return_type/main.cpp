// N5008 [expr.prim.req.compound]/1: a compound-requirement
// `{ E } -> C;` is satisfied when E is a valid expression AND
// C<decltype((E))> is satisfied.  CBMC gets the FALSE case right (a type
// without the operator does not satisfy the requirement) but evaluates
// the SATISFIED cases as false too -- the return-type-requirement never
// holds.  libc++'s incrementable_traits uses exactly this shape
//   concept __has_integral_minus =
//     requires(const _Tp& __x, const _Tp& __y) { { __x - __y } -> integral; };
// to detect difference_type, so difference_type/iterator_traits come out
// wrong for every iterator and the C++20 ranges chain misbehaves --
// the suspected remaining blocker of cpp20_ranges_basic_libcxx.
// g++ and clang++ both accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct is_int_
{
  static const bool value = false;
};
template <> struct is_int_<int>
{
  static const bool value = true;
};
template <class T>
concept integral_ = is_int_<T>::value;
template <class T>
concept has_integral_minus = requires(const T &a, const T &b) {
  { a - b } -> integral_;
};
struct no_minus
{
  int x;
};
struct with_minus
{
  int x;
  int operator-(const with_minus &o) const
  {
    return x - o.x;
  }
};
int main()
{
  bool a = has_integral_minus<no_minus>;
  bool b = has_integral_minus<with_minus>;
  bool c = has_integral_minus<int>;
  __CPROVER_assert(!a, "absent operator- => false");
  __CPROVER_assert(b, "present operator- => true");
  __CPROVER_assert(c, "int => true");
  return 0;
}
