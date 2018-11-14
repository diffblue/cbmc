/*******************************************************************\

Module:

Author: Diffblue Ltd

\*******************************************************************/


#ifndef CPROVER_UTIL_CONST_CAST_ITERATOR_H
#define CPROVER_UTIL_CONST_CAST_ITERATOR_H

template <typename Container, typename ConstIterator>
typename Container::iterator get_nonconst_iterator(
  Container& c, ConstIterator it)
{
  return c.erase(it, it);
}

#endif // CPROVER_UTIL_CONST_CAST_ITERATOR_H
