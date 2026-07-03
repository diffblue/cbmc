// N5008 [dcl.init.ref]/5: a non-const lvalue reference binds only to an lvalue;
// an rvalue argument can bind only to a const lvalue reference or an rvalue
// reference.  Overload resolution for a converting constructor must therefore
// treat a `T(X&)` candidate (non-const lvalue-reference parameter) as NOT
// viable for an rvalue argument.
//
// This surfaced when the `__is_constructible` intrinsic is queried twice for
// the same target type with different argument value categories.  A
// forwarding-reference converting-constructor template `T(U&&)` deduces
// `U = X&` for the lvalue query (is_constructible<T, X&>) and `U = X` for the
// rvalue query (is_constructible<T, X&&>).  Evaluating the first query
// instantiates the concrete constructor `T(X&)` as a class member; the second
// query's converting-constructor scan then reached that `T(X&)` candidate with
// an rvalue argument.  Lacking the [dcl.init.ref]/5 viability check, CBMC tried
// to bind the rvalue to `X&` and aborted type-checking with "invalid implicit
// conversion from X to X&", which dropped the enclosing function's body (so its
// assertions silently vanished).
//
// `W` models std::reference_wrapper's dangling guard (constructible from an
// lvalue, not from an rvalue).  Both queries must evaluate -- to true and false
// respectively -- and main() must survive.  g++ and clang++ agree.
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
  static void S(T &&) = delete;
  template <class U, class = decltype(S(declval<U>()))>
  W(U &&u) : p(&static_cast<T &>(u))
  {
  }
};

int main()
{
  // Two queries on the SAME target type with different argument value
  // categories: the lvalue is constructible, the rvalue is not.
  const bool from_lvalue = __is_constructible(W<const int>, int &);
  const bool from_rvalue = __is_constructible(W<const int>, int &&);
  __CPROVER_assert(
    from_lvalue && !from_rvalue,
    "two is_constructible queries on one type resolve independently");
  __CPROVER_assert(
    !(from_lvalue && !from_rvalue), "WRONG must FAIL");
  return 0;
}
