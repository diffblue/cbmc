// N5008 [temp.variadic]/5: a pack-expansion use of a function parameter pack in
// a function body -- here the call `fp(a...)` in `go`, where `a` is the
// parameter pack of `go(A... a)` and `A` is the enclosing class template
// parameter pack -- must expand to one argument per pack element.
//
// With the member function-pointer type expanded to full arity (see
// cpp11_variadic_pack_in_member_funptr_type), the field `fp` has type
// int(*)(int,int) and binds `add`.  The body call `fp(a...)` must then expand to
// `fp(a$0, a$1)`.  When the member belongs to a partial-specialization class
// C<R(A...)> instantiated via template_mapt, the replicated parameters are
// named base$k and cpp_typecheck_method_bodies recovers the pack count from
// those names (no in-class #expanded_param_packs record exists on that path).
// This is the libstdc++ function<_Res(_ArgTypes...)>::operator() body shape
// `_M_invoker(_M_functor, std::forward<_ArgTypes>(__args)...)`.
//
// Header-free and non-vacuous (assertion 2 must FAIL).

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
