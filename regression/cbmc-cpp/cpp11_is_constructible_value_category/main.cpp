// N5008 [meta.unary.prop]: `is_constructible<T, Args...>` is defined in terms of
// the variable definition `T obj(declval<Args>()...)`.  `declval<Arg>()` is an
// lvalue if and only if `Arg` is an lvalue-reference type; otherwise it is an
// xvalue (rvalue).  This value category matters when a constructor is a
// forwarding reference `T(U&&)`: an lvalue argument deduces `U = int&`, an
// rvalue deduces `U = int`.
//
// The classic use is std::reference_wrapper<const T>, whose converting
// constructor is SFINAE-constrained by an overload set that DELETES the rvalue
// form (to prevent binding a reference to a temporary).  Hence a
// reference_wrapper is constructible from `T&` but not from `T&&` or `T`.
//
// CBMC's `__is_constructible` intrinsic built the candidate source expression
// from the de-referenced argument type without recording its value category,
// so an lvalue-reference argument was treated as an rvalue: the forwarding
// reference deduced the rvalue form and selected the deleted overload, wrongly
// reporting is_constructible<reference_wrapper<const int>, int&> as false.
// That broke, e.g., constructing std::optional<std::reference_wrapper<const
// array_exprt>> in simplify_utils.cpp.
//
// `W` models reference_wrapper's dangling guard: it is constructible from an
// lvalue (`int&`) but not from an rvalue.  With the fix, the intrinsic returns
// true for the lvalue-reference argument, matching g++ and clang++.
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval() noexcept;

template <class T>
struct W
{
  T *p;
  static void S(T &) noexcept;
  static void S(T &&) = delete; // reject rvalues (dangling guard)
  template <class U, class = decltype(S(declval<U>()))>
  W(U &&u) : p(&static_cast<T &>(u))
  {
  }
};

int main()
{
  // Argument is an lvalue reference, so declval<int&>() is an lvalue and the
  // forwarding-reference constructor deduces U = int&, selecting the viable
  // S(T&) overload -- so W<const int> IS constructible from int&.
  const bool from_lvalue = __is_constructible(W<const int>, int &);
  __CPROVER_assert(
    from_lvalue, "constructible from an lvalue (S(T&) binds, deleted S(T&&) not)");
  __CPROVER_assert(!from_lvalue, "WRONG must FAIL");
  return 0;
}
