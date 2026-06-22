// [expr.const] / [temp.inst]: a call to a constexpr static member function
// *template* with explicit template arguments must be usable as a constant
// expression.  CBMC evaluates a plain constexpr function call as a constant
// (and would here too), but a constexpr static member function template call
// resolves to the generic (un-instantiated) template -- whose body still
// references the template parameter -- so the constexpr mini-interpreter cannot
// fold it and it is rejected with "expected constant expression, but got
// 'ok()'".  This is the blocker for std::get<i> on a std::tuple: libstdc++'s
// tuple constructors are constrained by constexpr static member function
// templates (_TupleConstraints::__is_explicitly_constructible<...>() etc.)
// evaluated in the constructors' enable_if conditions.

struct TC
{
  template <class U>
  static constexpr bool ok()
  {
    return sizeof(U) >= 1;
  }
};

template <bool C>
struct S
{
  static const int value = C ? 7 : 0;
};

int main()
{
  // TC::ok<int>() is a constexpr member-function-template call; it must be a
  // constant expression usable as a template argument.
  __CPROVER_assert(
    S<TC::ok<int>()>::value == 7, "constexpr member fn template as constant");
  return 0;
}
