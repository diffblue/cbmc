// N5008 [temp.variadic]/8-9: a pack expansion is expanded by the packs
// named in its pattern.  `Args...` in the body of inv expands inv's own
// pack, also when inv is instantiated from a caller whose own pack has
// one element (call(f) calls inv(F(), x..., 0), so Args is {F, int}).
template <class T>
T &&declval();
template <class T>
struct success
{
  using type = T;
};
template <class Fn, class... A>
success<char[sizeof...(A) + 1]> count_args(int);
template <class Fn, class... A>
success<decltype(Fn()(declval<A>()...))> call_result(int);
template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};

struct P
{
};
struct Base
{
  P operator()(...)
  {
    return P{};
  }
};
struct F : Base
{
  template <class R, class G>
  long operator()(R, G);
  using Base::operator();
};

template <class C, class... Args>
int inv(C, Args...)
{
  return (int)sizeof(typename decltype(count_args<C, Args...>(0))::type) - 1;
}
template <class C, class... Args>
bool inv_result(C, Args...)
{
  return same<typename decltype(call_result<C, Args...>(0))::type, long>::value;
}
template <class... X>
int call(X... x)
{
  return inv(F(), x..., 0);
}
template <class... X>
bool call_result_of(X... x)
{
  return inv_result(F(), x..., 0);
}

int main()
{
  F f;
  __CPROVER_assert(call(f) == 2, "one-element caller pack: two arguments");
  __CPROVER_assert(call(f, f) == 3, "two-element caller pack");
  __CPROVER_assert(call_result_of(f), "two-parameter operator() selected");
  __CPROVER_assert(call(f) != 2, "WRONG (must FAIL)");
}
