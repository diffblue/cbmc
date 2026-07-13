// N5008 [temp.alias]/2 + [temp.deduct.type] + [temp.variadic]/4-5: deducing a
// parameter pack THROUGH an alias template that maps the pack onto a class
// template with a fixed leading argument:
//
//   template <class T, T... I> struct iseq {};
//   template <SIZE... I> using idxseq = iseq<SIZE, I...>;      // fixed T = SIZE
//   template <SIZE... J> int apply_impl(idxseq<J...>) { ... }  // deduce J
//
// This is exactly std::index_sequence
// (`template <size_t... _Idx> using index_sequence = integer_sequence<size_t,
// _Idx...>`), the parameter type of std::apply's __apply_impl.
//
// CORE (was KNOWNBUG): guess_template_args substituted the alias's parameters
// into the aliased-type pattern using ID_C_base_name, which is empty for a
// non-type parameter (stored as a symbol whose name is only the suffix of its
// scoped identifier), so the substitution never fired and the enclosing
// function's pack was never deduced ("found no match").  Fixed by deriving the
// alias parameter's base name robustly.  Covers a NON-type pack and a TYPE pack,
// each with a deducing-function pack name DIFFERENT from the alias's own
// parameter name (so it is a genuine substitution, not an accidental name
// match).
//
// g++ compiles and runs these values; clang++ accepts.  Non-vacuous: each
// assertion is a concrete function of the deduced pack.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <class T, T... I>
struct iseq
{
};

// non-type parameter pack through an alias (std::index_sequence shape)
template <__SIZE_TYPE__... I>
using idxseq = iseq<__SIZE_TYPE__, I...>;

template <__SIZE_TYPE__... J>
int sum_impl(idxseq<J...>)
{
  return add(J...);
}

// type parameter pack through an alias with a fixed leading type argument
template <class... U>
struct tseq
{
};

template <class... U>
using talias = tseq<int, U...>;

template <class... W>
int count_impl(talias<W...>)
{
  return sizeof...(W);
}

int main()
{
  __CPROVER_assert(sum_impl(idxseq<1, 2>{}) == 3, "non-type alias pack: 1+2==3");
  __CPROVER_assert(
    count_impl(talias<char, char, char>{}) == 3, "type alias pack: count==3");
  return 0;
}
