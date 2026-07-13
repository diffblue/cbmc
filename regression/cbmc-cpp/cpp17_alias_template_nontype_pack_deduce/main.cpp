// N5008 [temp.alias]/2 + [temp.deduct.type] + [temp.variadic]/4-5: the core of
// the remaining cpp17_apply_basic blocker.  A NON-type parameter pack is
// deduced through an ALIAS TEMPLATE that maps the pack onto a class template
// with a fixed leading argument:
//
//   template <class T, T... I> struct iseq {};
//   template <SIZE... I> using idxseq = iseq<SIZE, I...>;      // fixed T = SIZE
//   template <SIZE... J> int apply_impl(idxseq<J...>) { ... }  // deduce J
//
// This is exactly std::index_sequence:
//   template <size_t... _Idx> using index_sequence
//     = integer_sequence<size_t, _Idx...>;
// and the std::apply helper's parameter `index_sequence<_Idx...>`.
//
// KNOWNBUG: CBMC fails to deduce the pack through the alias -- "found no match
// for symbol 'apply_impl'" -- so the call does not resolve.  Deducing directly
// from the underlying class template `iseq<SIZE, J...>` (without the alias)
// works; the defect is specific to a pack deduced THROUGH the alias, whose
// aliased-type pattern must be substituted with the deducing function's pack
// before matching.  (A hand-written alias happens to succeed only when the
// deducing function's pack parameter is spelled identically to the alias's own
// pack parameter -- an accidental name-based match; the real std::index_sequence
// fails regardless.)
//
// This blocks std::apply, whose __apply_impl deduces `size_t... _Idx` from
// `make_index_sequence<...>` (an index_sequence alias specialisation).
//
// g++ compiles and runs r == 3; clang++ accepts.  Flip to CORE once a non-type
// pack is deduced through an alias template.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <class T, T... I>
struct iseq
{
};

template <__SIZE_TYPE__... I>
using idxseq = iseq<__SIZE_TYPE__, I...>;

template <__SIZE_TYPE__... J>
int apply_impl(idxseq<J...>)
{
  return add(J...);
}

int main()
{
  __CPROVER_assert(apply_impl(idxseq<1, 2>{}) == 3, "alias-pack deduce sum==3");
  return 0;
}
