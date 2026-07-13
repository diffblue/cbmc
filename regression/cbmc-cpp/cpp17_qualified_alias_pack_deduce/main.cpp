// N5008 [temp.alias]/2 + [temp.deduct.type] + [temp.variadic]/4-5: deducing a
// parameter pack through a QUALIFIED alias template.  The unqualified case is
// cpp17_alias_template_nontype_pack_deduce; this is the same deduction with the
// alias named through a qualifier -- exactly how std::apply uses
// `std::index_sequence<_Idx...>` (a qualified alias for
// `std::integer_sequence<size_t, _Idx...>`).
//
// CORE (was KNOWNBUG): the alias-expansion branch in guess_template_args was
// restricted to UNqualified template-ids, because it looked the alias up by
// base name recursively -- which for a qualified name found the wrong symbol
// and looped (the libstdc++ regex member-alias shape).  A qualified alias was
// therefore never expanded and its pack was not deduced ("found no match").
// Fixed by resolving a qualified alias template-id through its qualifiers
// (resolve_scope + QUALIFIED lookup), restoring the scope resolve_scope moves,
// before re-deducing.  Proper qualified lookup resolves an alias's own
// expansion target to the class template, so expansion terminates without the
// unqualified-only restriction.
//
// Covers a hand-written namespaced qualified alias for both a non-type and a
// type pack.  g++ compiles and runs these values; clang++ accepts.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

namespace N
{
template <class T, T... I>
struct iseq
{
};

// non-type pack through a qualified alias (std::index_sequence shape)
template <__SIZE_TYPE__... I>
using idxseq = iseq<__SIZE_TYPE__, I...>;

template <class... U>
struct tseq
{
};

// type pack through a qualified alias with a fixed leading type argument
template <class... U>
using talias = tseq<int, U...>;
}

template <__SIZE_TYPE__... J>
int sum_impl(N::idxseq<J...>)
{
  return add(J...);
}

template <class... W>
int count_impl(N::talias<W...>)
{
  return sizeof...(W);
}

int main()
{
  __CPROVER_assert(
    sum_impl(N::idxseq<1, 2>{}) == 3, "qualified non-type alias pack: 1+2==3");
  __CPROVER_assert(
    count_impl(N::talias<char, char, char>{}) == 3,
    "qualified type alias pack: count==3");
  return 0;
}
