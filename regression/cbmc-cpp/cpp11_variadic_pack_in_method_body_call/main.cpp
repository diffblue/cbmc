// N5008 [temp.variadic]/5: a pack-expansion use of a function parameter pack in
// a function body -- here the call `fp(a...)` in `go`, where `a` is the
// parameter pack of `go(A... a)` and `A` is the enclosing class template
// parameter pack -- must expand to one argument per pack element.
//
// With the member function-pointer type now expanded to full arity (see
// cpp11_variadic_pack_in_member_funptr_type), the field `fp` correctly has type
// int(*)(int,int) and binds `add`, but the body call `fp(a...)` is expanded to a
// single argument, so the call is rejected ("wrong number of function
// arguments: expected 2, but got 1").  This is the libstdc++
// function<_Res(_ArgTypes...)>::operator() body shape
// `_M_invoker(_M_functor, std::forward<_ArgTypes>(__args)...)`, the remaining
// blocker for multi-argument std::function invocation.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once the
// body pack-expansion uses the full deduced pack arity.

extern "C" void __CPROVER_assert(int, const char *);

template <class Sig>
struct Func;
template <class R, class... A>
struct Func<R(A...)>
{
  using Fp = R (*)(A...);
  Fp fp = nullptr;
  R go(A... a) { return fp(a...); } // body pack-expansion use of `a`
};

int add(int a, int b)
{
  return a + b;
}

int main()
{
  Func<int(int, int)> f;
  f.fp = add;
  int r = f.go(2, 3);
  __CPROVER_assert(r == 5, "body pack-expansion call expanded to full arity");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
