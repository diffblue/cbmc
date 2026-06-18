// [temp.variadic]/5 + [dcl.ref] (reference collapsing): a forwarding-reference
// parameter pack `A&&...` expands, for each element E, to the reference type
// E&& / E& -- not to a by-value E.
//
// This matters when the pack belongs to a class template partial specialization
// whose static member uses it, e.g. libstdc++'s
//   _Function_handler<R(A...), F>::_M_invoke(_Any_data&, A&&... __args)
// whose address is stored in std::function's member
//   R (*_M_invoker)(const _Any_data&, A&&...).
// If the `&&` is dropped while expanding the pack in `_M_invoke`, its type
// becomes R(*)(_Any_data&, int) which does not match the R(*)(_Any_data&, int&&)
// member, so `_M_invoker = &_Handler::_M_invoke` is rejected, the constructor
// body is left empty, and every std::function call dereferences a null
// function pointer.

template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template <typename T>
struct decay
{
  typedef T type;
};
template <typename A, typename B>
struct is_same
{
  static const bool value = false;
};
template <typename A>
struct is_same<A, A>
{
  static const bool value = true;
};

struct Data
{
  char buf[8];
};

template <typename Sig, typename F>
struct fhandler;
template <typename R, typename... A, typename F>
struct fhandler<R(A...), F>
{
  // Forwarding-reference pack after a leading parameter.
  static R invoke(const Data &, A &&...) { return (R)5; }
};

template <typename Sig>
struct myfunc;
template <typename R, typename... A>
struct myfunc<R(A...)>
{
  R (*invoker)(const Data &, A &&...);
  Data data;
  myfunc() : invoker(0) {}
  template <typename F,
            typename = typename enable_if<!is_same<F, myfunc>::value>::type>
  myfunc(F &&)
  {
    typedef fhandler<R(A...), typename decay<F>::type> H;
    invoker = &H::invoke;
  }
  R operator()(A... a) const { return invoker(data, static_cast<A &&>(a)...); }
};

struct Fn
{
  int operator()(int) const { return 5; }
};

int main()
{
  myfunc<int(int)> f = Fn{};
  __CPROVER_assert(
    f.invoker != 0, "forwarding-ref pack member function address is assigned");
  __CPROVER_assert(f(0) == 5, "type-erased call through the forwarding-ref pack");
  return 0;
}
