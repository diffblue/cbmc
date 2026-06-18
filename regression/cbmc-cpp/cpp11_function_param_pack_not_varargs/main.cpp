// [temp.variadic]/3 + [dcl.fct]: a `...` that immediately follows a parameter
// declaration with no separating comma -- e.g. `f(Args...)` where Args is a
// template parameter pack -- introduces a function parameter pack.  It is NOT a
// C-style variadic ellipsis (which is written with a preceding comma,
// `f(T, ...)`, or alone, `f(...)`).
//
// CBMC previously parsed `f(Args...)` (pack at the end of the parameter list)
// as the parameter `Args` followed by a separate C-style ellipsis, so the
// instantiated function type gained a spurious variadic `...`.  Taking the
// address of such a member then produced a type `R(*)(int, ...)` that did not
// match a concrete `R(*)(int)`, triggering an invariant violation
// ("symbol type must match") -- exactly the shape of libstdc++'s
// _Function_handler<R(Args...), F>::_M_invoke used by std::function.

template <typename Sig>
struct handler;
template <typename R, typename... Args>
struct handler<R(Args...)>
{
  static R val(Args...) { return (R)7; }
};

int main()
{
  // The address of the partial-specialization's static member has type
  // int(*)(int) -- no spurious variadic ellipsis -- so it binds to fp.
  int (*fp)(int) = &handler<int(int)>::val;
  __CPROVER_assert(fp != 0, "address of pack static member has non-varargs type");
  __CPROVER_assert(fp(3) == 7, "the pack-parameter function is callable");
  return 0;
}
