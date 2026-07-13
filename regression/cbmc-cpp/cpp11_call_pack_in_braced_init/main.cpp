// N5008 [temp.variadic]/5 + [dcl.init.aggr]: a variadic function template whose
// body expands a pack of CALLS inside a BRACED (aggregate) initializer:
//
//   template <class... E> box mk(E&&... e) { return box{fwd(e)...}; }
//
// This is the shape of libstdc++ std::make_tuple / the tuple forwarding
// constructor, whose member-initializer / return forwards each element
// (`std::forward<_Elements>(__args)...`) into the aggregate/base.
//
// KNOWNBUG: the pack expansion of the call `fwd(e)...` inside the braced
// initializer is not performed when the (deferred) function-template body is
// instantiated, so the body is dropped entirely -- "no body for callee
// mk<int,int>" -- and the call returns a nondeterministic value.  The SAME
// call-pack inside a function-CALL argument list (`sum(fwd(e)...)`) IS handled;
// so is a braced initializer without a call (`box{e...}`).  The defect is
// specific to a call-pack inside a braced/aggregate initializer.
//
// This is the root of cpp17_tuple_basic: std::make_tuple<int,int,int> is left
// without a body (returns a nondeterministic tuple), so std::get reads garbage.
//
// g++ compiles and runs a == 10, b == 20; clang++ accepts.  Flip to CORE once a
// call-pack in a braced initializer is expanded in a deferred body.
//
// Non-vacuous: the assertion is a concrete function of the forwarded arguments;
// under the dropped-body behaviour the result is nondeterministic.

extern "C" void __CPROVER_assert(int, const char *);

struct box2
{
  int a, b;
};

template <class T>
T &&fwd(T &x)
{
  return static_cast<T &&>(x);
}

template <class... E>
box2 mk(E &&... e)
{
  return box2{fwd(e)...};
}

int main()
{
  auto b = mk(10, 20);
  __CPROVER_assert(b.a == 10 && b.b == 20, "call-pack in braced init: {10,20}");
  return 0;
}
