#include <algorithm>
#include <iterator>

template<class containert>
typename containert::iterator copy_iterator(const containert &old_container,
    containert &new_container, typename containert::const_iterator it)
{
  const typename containert::iterator empty;
  if (empty == it) return empty;
  const size_t old_distance=std::distance(old_container.begin(), it);
  typename containert::iterator new_it=new_container.begin();
  std::advance(new_it, old_distance);
  return new_it;
}

template<class containert, class iterator_containert>
iterator_containert copy_iterators(const containert &old_container,
    containert &new_container, const iterator_containert &iterators)
{
  iterator_containert new_iterators;
  std::transform(iterators.begin(), iterators.end(),
      std::back_inserter(new_iterators),
      [&old_container, &new_container](const typename containert::const_iterator it)
      { return copy_iterator(old_container, new_container, it);});
  return new_iterators;
}
