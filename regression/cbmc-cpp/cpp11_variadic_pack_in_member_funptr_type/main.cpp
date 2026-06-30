// N5008 [temp.variadic]/5: a pack expansion `A...` of a class template
// parameter pack that appears in the type of a (non-function) data member --
// here the parameter list of a member function-pointer type `R (*)(A...)` --
// must expand to one element per pack member when the class template partial
// specialization `Func<R(A...)>` is instantiated.
//
// This is the shape of libstdc++'s `function<_Res(_ArgTypes...)>::_M_invoker`,
// whose type `_Res (*)(const _Any_data&, _ArgTypes&&...)` was collapsed to a
// single parameter for a multi-argument signature, so the correctly-arity'd
// `&_Function_handler<_Res(A...), F>::_M_invoke` could not be assigned to it
// (the multi-argument std::function converting constructor then silently
// failed to elaborate).
//
// Header-free and non-vacuous (assertion 2 must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

template <class Sig>
struct Func;
template <class R, class... A>
struct Func<R(A...)>
{
  using Fp = R (*)(A...); // pack expansion inside a member type
  Fp fp = nullptr;
};

int add(int a, int b)
{
  return a + b;
}

int main()
{
  Func<int(int, int)> f;
  f.fp = add; // binds only if Fp is int(*)(int,int), not the collapsed int(*)(int)
  int r = f.fp(2, 3);
  __CPROVER_assert(r == 5, "member function-pointer pack expanded to full arity");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
