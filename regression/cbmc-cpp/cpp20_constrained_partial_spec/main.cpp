// C++20 selection among class-template partial specializations that share the
// same template-argument pattern and differ only by their requires-clauses
// ([temp.class.spec.match]/1-2 with [temp.constr.order]).
//
// This is the shape of libstdc++'s std::__iterator_traits<_Iterator, void>,
// whose three specializations are distinguished solely by their constraints
// (__detail::__iter_with_nested_types vs __iter_without_nested_types && ...).
// The most-constrained *satisfied* specialization must be selected: here
// with_cat has a nested ::cat, so the has_cat-constrained specialization wins
// and traits<with_cat>::cat is char, not the no_cat fallback int.
#include <type_traits>

namespace d
{
template <typename T>
concept has_cat = requires { typename T::cat; };
template <typename T>
concept no_cat = !requires { typename T::cat; };
}

template <typename T, typename = void>
struct traits
{
};

template <typename T>
  requires d::has_cat<T>
struct traits<T, void>
{
  using cat = typename T::cat;
};

template <typename T>
  requires d::no_cat<T>
struct traits<T, void>
{
  using cat = int;
};

struct with_cat
{
  typedef char cat;
};

int main()
{
  __CPROVER_assert(
    std::is_same<traits<with_cat>::cat, char>::value,
    "constrained partial specialization selected by requires-clause");
  return 0;
}
