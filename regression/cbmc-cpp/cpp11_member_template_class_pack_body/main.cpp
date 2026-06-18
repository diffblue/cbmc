// [temp.variadic] + [temp.mem]: a member function template of a class template
// that is partial-specialized on a function type R(Args...) may, in its body,
// use the enclosing class's parameter pack Args... to form a template argument
// -- e.g. reconstruct the function type R(Args...) to instantiate another
// template.  Such a member template's body must be instantiated normally.
//
// This is exactly std::function's converting constructor, whose body is
//   typedef _Function_handler<_Res(_ArgTypes...), _Functor> _Handler;
//   ...
//   _M_invoker = &_Handler::_M_invoke;
// where _ArgTypes is the class template parameter pack.
//
// KNOWNBUG: CBMC leaves the body of such a member function template
// uninstantiated (an empty body / "no body for callee"), so the constructor is
// a no-op.  For std::function this means _M_invoker is never assigned, and
// every std::function call dereferences a null function pointer.  Here the
// equivalent member `invoker` is left null and `call()` dereferences null.
// Reclassify CORE once the member template's body is instantiated.

template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};

template <typename Sig, typename F>
struct handler;
template <typename R, typename... Args, typename F>
struct handler<R(Args...), F>
{
  static R invoke(Args... a) { return (R)42; }
};

template <typename Sig>
struct func;
template <typename R, typename... Args>
struct func<R(Args...)>
{
  R (*invoker)(Args...);
  // The body uses the enclosing class's parameter pack Args... to form the
  // template argument R(Args...).
  template <typename F, typename = typename enable_if<true>::type>
  func(F &&)
  {
    invoker = &handler<R(Args...), F>::invoke;
  }
  R call(Args... a) const { return invoker(a...); }
};

int main()
{
  auto lam = [](int x) { return x; };
  func<int(int)> f(lam);
  __CPROVER_assert(
    f.call(5) == 42,
    "member-template ctor reconstructing the class pack has its body "
    "instantiated");
  return 0;
}
