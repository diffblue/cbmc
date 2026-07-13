// N5008 [temp.spec.partial] + [temp.variadic]/4-5: a VARIABLE TEMPLATE partial
// specialization whose pattern deduces a parameter PACK:
//
//   template <class T>    constexpr unsigned long tsize_v            = 99;
//   template <class... E> constexpr unsigned long tsize_v<tup<E...>> = sizeof...(E);
//
// This is exactly libstdc++'s std::tuple_size_v
// (`inline constexpr size_t tuple_size_v<tuple<_Types...>> = sizeof...`), which
// std::apply uses to size its index sequence.
//
// CORE (was KNOWNBUG): the variable-template partial-specialization matcher
// instantiated the best match with build_template_args' single scalar
// placeholder per pack, so the deduced pack collapsed to ONE element
// (tsize_v<tup<int,int>> evaluated to 1).  Fixed by expanding a deduced pack to
// one argument per element before instantiating, mirroring the class
// partial-spec expansion.
//
// Covers the hand-written shape (sizes 2 and 3) and the real std::tuple_size_v.
// g++ static_asserts and runs these values; clang++ accepts.  Non-vacuous: each
// assertion is a concrete function of the deduced pack arity.

#include <tuple>

extern "C" void __CPROVER_assert(int, const char *);

template <class...>
struct tup
{
};

template <class T>
constexpr unsigned long tsize_v = 99;

template <class... E>
constexpr unsigned long tsize_v<tup<E...>> = sizeof...(E);

int main()
{
  unsigned long v2 = tsize_v<tup<int, int>>;
  unsigned long v3 = tsize_v<tup<int, int, int>>;
  __CPROVER_assert(v2 == 2, "pack variable-template partial spec: size 2");
  __CPROVER_assert(v3 == 3, "pack variable-template partial spec: size 3");

  unsigned long r2 = std::tuple_size_v<std::tuple<int, int>>;
  __CPROVER_assert(r2 == 2, "real std::tuple_size_v: size 2");
  return 0;
}
