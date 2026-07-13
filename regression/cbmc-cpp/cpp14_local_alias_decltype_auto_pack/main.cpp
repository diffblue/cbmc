// N5008 [dcl.spec.auto]/2-3 + [temp.variadic]/5: a function template with a
// DEDUCED return type (`decltype(auto)`) whose body declares a LOCAL type alias
// and uses it to construct the argument of a nested deduced-return call:
//
//   template <class T> decltype(auto) outer(T)
//   { using Ind = seq<0, 1>; return inner(Ind{}); }   // inner is decltype(auto)
//
// This is the shape of libstdc++ std::apply's body
//   using _Indices = make_index_sequence<tuple_size_v<remove_reference_t<_Tuple>>>;
//   return std::__apply_impl(..., _Indices{});
//
// CORE (was KNOWNBUG): the return type could not be typed from the return
// expression in isolation (the body-local alias `Ind` was not yet in scope), so
// deduction was deferred; but typecheck_return then tried to convert the return
// value to the still-unresolved `<<type:decltype>>` and aborted.  Fixed by
// deducing a `decltype(auto)` return type in typecheck_return without a
// conversion (as for plain `auto`).
//
// g++ compiles and runs these values; clang++ accepts.  Non-vacuous: each
// result is a concrete function of the pack carried by the local alias.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

template <int...>
struct seq
{
};

template <int... I>
decltype(auto) inner(seq<I...>)
{
  return add(I...);
}

template <int... I>
decltype(auto) inner3(seq<I...>)
{
  return add3(I...);
}

// local alias to a fixed sequence
template <class T>
decltype(auto) outer(T)
{
  using Ind = seq<0, 1>;
  return inner(Ind{});
}

// local alias that DEPENDS on the template parameter
template <class T>
struct mk
{
  using type = seq<1, 2, 3>;
};

template <class T>
decltype(auto) outer3(T)
{
  using Ind = typename mk<T>::type;
  return inner3(Ind{});
}

int main()
{
  __CPROVER_assert(outer(0) == 1, "local alias seq<0,1>: 0+1==1");
  __CPROVER_assert(outer3(0) == 6, "dependent local alias seq<1,2,3>: 1+2+3==6");
  return 0;
}
