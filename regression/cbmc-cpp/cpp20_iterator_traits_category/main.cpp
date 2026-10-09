// C++20 std::iterator_traits<__normal_iterator<...>>::iterator_category.
//
// For a class iterator, std::iterator_traits derives from __iterator_traits,
// whose meaningful definition (under __cpp_lib_concepts) is a *constrained*
// partial specialization selected by its requires-clause
// (__detail::__iter_with_nested_types) per [temp.class.spec.match] and
// [temp.constr].  That specialization exposes
//   iterator_category = typename _Iterator::iterator_category,
// so for std::vector<int>::iterator (a random-access __normal_iterator) the
// category is std::random_access_iterator_tag ([iterator.traits]).
#include <iterator>
#include <type_traits>
#include <vector>

int main()
{
  typedef std::vector<int>::iterator It;
  bool is_rai = std::is_same<
    typename std::iterator_traits<It>::iterator_category,
    std::random_access_iterator_tag>::value;
  __CPROVER_assert(is_rai, "vector iterator category is random_access");
  return 0;
}
