// C++ [temp.variadic]/4-5 + [temp.names]: a parameter pack used as a template
// argument (Trait<A...>) instantiates the class template with the pack's
// elements; the dependent qualified-id Trait<A...>::type then names a member of
// that instance.  Here the pack A is a *deduced* function-template parameter
// pack, and the class trait's member is a plain typedef (no decltype involved),
// so this isolates the template-argument / qualified-id pack-expansion path.
//
// KNOWNBUG: when Trait<A...> is instantiated with a deduced pack during nested
// instantiation, the pack argument is collapsed/lost rather than expanded into
// the class template's own parameter pack, so first_type<A...>::type does not
// resolve correctly and the enclosing function's instantiated body is dropped
// (it returns a nondeterministic value, so the size check fails).
//
// The same gap (with a decltype-valued member) is cpp11_decltype_pack_in_class_
// template; this is the header-free, decltype-free isolation.  Reclassify CORE
// once a deduced pack used as a class-template argument is expanded so the
// qualified-id names the correct member.

template <typename First, typename... Rest>
struct first_type
{
  typedef First type;
};

template <typename... A>
unsigned pick(A... a)
{
  (void)sizeof...(a);
  // first_type<A...>::type names the first element type of the pack.
  return sizeof(typename first_type<A...>::type);
}

int main()
{
  // first_type<long long, char, int>::type == long long -> sizeof 8.
  __CPROVER_assert(
    pick((long long)0, (char)0, (int)0) == 8,
    "first_type<A...>::type resolves to long long (8 bytes)");
  return 0;
}
