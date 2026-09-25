// N5008 [temp.variadic]/4-5: a pack expansion `P...` produces one element per
// element of the pack `P`, whether `P` is a type or a NON-type parameter pack.
//
// Forwarding a non-type parameter pack `T...` into another template-argument
// list (`cnt<T...>`) must preserve its arity.  This previously collapsed to a
// single element for two or more elements, because a non-type pack was
// scalar-bound to its first argument in the template map (the collapse the
// front-end already avoids for type packs).  Now fixed.
//
// CORE (was KNOWNBUG cpp11_nontype_pack_forward_collapse).  Non-vacuous: under
// the old collapse each `n` would be 1, so every assertion below would fail.

extern "C" void __CPROVER_assert(int, const char *);

template <int... V>
struct cnt
{
  static constexpr int n = sizeof...(V);
};

template <int... T>
struct fwd
{
  static constexpr int n = cnt<T...>::n;
};

int main()
{
  __CPROVER_assert(fwd<>::n == 0, "0 elements");
  __CPROVER_assert(fwd<5>::n == 1, "1 element");
  __CPROVER_assert(fwd<2, 3>::n == 2, "2 elements");
  __CPROVER_assert(fwd<1, 2, 3, 4>::n == 4, "4 elements");
  return 0;
}
