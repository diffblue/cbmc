// Pack expansion of a dependent member-alias pattern in a template argument
// list: Container<typename Trait<E>::member...> (N5008 [temp.variadic]/4-5).
// The pattern's pack E is nested inside the pattern and must be expanded once
// per element (this is the shape of std::make_tuple's return type,
// tuple<typename __decay_and_strip<E>::__type...>).

template <class T>
struct identity
{
  using type = T;
};

template <class... E>
struct box
{
};

// Deduce the pack from a box to recover its arity.
template <class... E>
int arity(box<E...>)
{
  return sizeof...(E);
}

// Return type uses a pack expansion whose pattern nests the pack E.
template <class... E>
box<typename identity<E>::type...> make_box()
{
  return {};
}

int main()
{
  // identity<E>::type is E, so make_box<...>() returns box<...> with the
  // same element count; without per-element expansion the pack would
  // collapse to a single element.
  __CPROVER_assert(arity(make_box<int, double, char>()) == 3, "three elements");
  __CPROVER_assert(arity(make_box<int>()) == 1, "one element");
  // NOTE: the empty-explicit-pack case make_box<>() ([temp.arg.explicit]/4:
  // a trailing pack not otherwise deduced is an empty sequence) is a separate
  // latent bug -- CBMC drops make_box<>() -- and is covered by the KNOWNBUG
  // cpp11_variadic_empty_explicit_pack.
  return 0;
}
