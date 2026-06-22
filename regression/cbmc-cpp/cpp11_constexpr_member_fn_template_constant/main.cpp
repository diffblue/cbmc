// [temp.inst]/5 + [expr.const]: a call to a constexpr static member function
// *template* with explicit template arguments must be usable as a constant
// expression, which requires the specialization's definition to be implicitly
// instantiated.  CBMC previously left such a member function template
// uninstantiated at constant-evaluation time -- its body, type-checked lazily
// for an ordinary member, was unavailable while the enclosing expression was
// being folded -- so the call could not be evaluated ("expected constant
// expression, but got 'ok()'").  CBMC now type-checks (instantiates) the
// definition of a constexpr member function template specialization eagerly,
// mirroring free function template specializations.
//
// This is the shape of libstdc++'s std::tuple constructor SFINAE
// (_TupleConstraints::__assignable<...>() etc.).

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
  // (1) a constexpr member function template call as a template argument.
  __CPROVER_assert(
    B<TC::ok<int>()>::value == 7, "constexpr member fn template as constant");

  // (2) a value that depends on the template argument, folded in a constant
  // context.
  __CPROVER_assert(
    V<TC::sz<int>()>::value == sizeof(int), "sz<int> folds to a constant");

  // (3) the same call at run time.
  unsigned r = TC::sz<int>();
  __CPROVER_assert(r == sizeof(int), "runtime constexpr member fn template");

  // (4) non-vacuity: a wrong value must FAIL, proving the folded constant is
  // genuinely computed and checked (not silently dropped).
  __CPROVER_assert(
    V<TC::sz<int>()>::value == 1, "WRONG sz<int>==1 (must FAIL)");
  return 0;
}
