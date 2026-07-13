// N5008 [temp.alias]/2 + [temp.deduct.type] + [temp.variadic]/4-5: deducing a
// parameter pack through a QUALIFIED alias template.  The unqualified case is
// handled (cpp17_alias_template_nontype_pack_deduce, CORE); this is the same
// deduction but the alias is named with a qualifier -- exactly how std::apply
// uses `std::index_sequence<_Idx...>` (a qualified alias for
// `std::integer_sequence<size_t, _Idx...>`).
//
// KNOWNBUG: the alias-expansion branch in guess_template_args is restricted to
// UNqualified template-ids (an anti-recursion guard for a libstdc++ regex
// member-alias shape), so a qualified alias is never expanded and the pack is
// not deduced -- "found no match for symbol 'f'".
//
// g++ compiles and runs r == 3; clang++ accepts.  This is the remaining
// cpp17_apply_basic blocker.  Flip to CORE once a qualified alias template's
// pack is deduced.

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

template <__SIZE_TYPE__... I>
using idxseq = iseq<__SIZE_TYPE__, I...>;
}

template <__SIZE_TYPE__... J>
int f(N::idxseq<J...>)
{
  return add(J...);
}

int main()
{
  __CPROVER_assert(f(N::idxseq<1, 2>{}) == 3, "qualified alias pack: 1+2==3");
  return 0;
}
