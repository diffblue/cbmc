// N5008 [dcl.spec.auto]/3 + [temp.variadic]/5: a function template with a
// DEDUCED return type (`decltype(auto)`) whose body declares a LOCAL type alias
// and uses it to construct the argument of a nested deduced-return call:
//
//   template <class T> decltype(auto) outer(T)
//   { using Ind = seq<0, 1>; return inner(Ind{}); }   // inner is decltype(auto)
//
// This is the shape of libstdc++ std::apply, whose body is
//   using _Indices = make_index_sequence<tuple_size_v<remove_reference_t<_Tuple>>>;
//   return std::__apply_impl(..., _Indices{});
//
// KNOWNBUG: outer's return type is not deduced -- the local alias `Ind` is not
// resolved during the eager return-type deduction, so `inner(Ind{})`'s type
// (and hence outer's) stays an unresolved `<<type:decltype>>` ("invalid
// implicit conversion from 'signed int' to '<<type:decltype>>'").  Here this is
// even instantiated and reaches goto-conversion, which aborts on the
// unresolved return type (a convert_return invariant); in cpp17_apply_basic the
// same root leaves std::apply's return type unresolved.  Using the sequence
// value INLINE (`inner(seq<0,1>{})`, no local alias) is handled correctly, as
// is the same code without the local alias.
//
// g++ compiles and runs r == 1; clang++ accepts.  Flip to CORE once a local
// type alias is resolved during return-type deduction of a decltype(auto)
// function.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
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

template <class T>
decltype(auto) outer(T)
{
  using Ind = seq<0, 1>;
  return inner(Ind{});
}

int main()
{
  // outer(0) -> inner(seq<0,1>{}) -> add(0, 1) == 1
  int r = outer(0);
  __CPROVER_assert(r == 1, "local-alias nested decltype(auto): 0+1==1");
  return 0;
}
