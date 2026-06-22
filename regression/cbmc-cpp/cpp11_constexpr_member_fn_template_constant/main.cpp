// [temp.inst]/5 + [expr.const]: a call to a constexpr static member function
// *template* with explicit template arguments must be usable as a constant
// expression -- which requires its specialization's definition to be
// implicitly instantiated.  CBMC previously left such a member function
// template uninstantiated (its body still referenced the template parameter),
// so the call could not be folded ("expected constant expression, but got
// 'ok()'"); worse, distinct specializations collided on a single unsuffixed
// member symbol, so e.g. sz<char> and sz<int> shared one body (unsound).
//
// This is the shape of libstdc++'s std::tuple constructor SFINAE
// (_TupleConstraints::__assignable<...>(), ...).

struct TC
{
  template <class U>
  static constexpr bool ok()
  {
    return sizeof(U) >= 1;
  }

  template <class U>
  static constexpr unsigned sz()
  {
    return sizeof(U);
  }
};

template <bool C>
struct B
{
  static const int value = C ? 7 : 0;
};

template <unsigned N>
struct V
{
  static const unsigned value = N;
};

int main()
{
  // (1) constexpr member function template call as a constant expression
  __CPROVER_assert(
    B<TC::ok<int>()>::value == 7, "constexpr member fn template as constant");

  // (2) distinct specializations must yield distinct, correct values
  // (regression for the unsuffixed-symbol collision).
  __CPROVER_assert(V<TC::sz<char>()>::value == 1, "sz<char> == 1");
  __CPROVER_assert(V<TC::sz<int>()>::value == sizeof(int), "sz<int> distinct");

  // (3) the same at run time: two specializations are independent entities.
  unsigned a = TC::sz<char>();
  unsigned b = TC::sz<int>();
  __CPROVER_assert(a == 1 && b == sizeof(int), "runtime: distinct bodies");

  // (4) non-vacuity: a wrong value must FAIL, proving the folded constant is
  // genuinely computed and checked.
  __CPROVER_assert(
    V<TC::sz<int>()>::value == 1, "WRONG sz<int>==1 (must FAIL)");
  return 0;
}
