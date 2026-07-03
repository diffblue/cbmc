// N5008 [temp.arg.explicit]/4: a trailing template parameter pack not otherwise
// deduced is deduced as an empty sequence.  So `make_box<>()` deduces the pack
// E as empty, returns `box<>` and `arity(make_box<>())` is 0.  g++ and clang++
// accept this and compute 0.
//
// KNOWN BUG: CBMC drops `make_box<>()` from the candidate set (the empty
// explicit template argument pack for a variadic function template whose return
// type is a nested-pack expansion is not resolved), leaving the call with no
// viable function ([temp.deduct]/8).  Previously this failure was silently
// swallowed and the call's assertion never checked; the SFINAE-enforcement fix
// now surfaces it as a CONVERSION ERROR.  Flip to CORE once make_box<>() is
// resolved.  The non-empty cases work and are covered (CORE) by
// cpp11_variadic_member_alias_pack.

template <class T>
struct identity
{
  using type = T;
};

template <class... E>
struct box
{
};

template <class... E>
int arity(box<E...>)
{
  return sizeof...(E);
}

template <class... E>
box<typename identity<E>::type...> make_box()
{
  return {};
}

extern "C" void __CPROVER_assert(int, const char *);

int main()
{
  __CPROVER_assert(arity(make_box<>()) == 0, "empty explicit pack -> arity 0");
  return 0;
}
