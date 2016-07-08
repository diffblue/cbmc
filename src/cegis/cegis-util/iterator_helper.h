/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CEGIS_UTIL_ITERATOR_HELPER_H_
#define CEGIS_UTIL_ITERATOR_HELPER_H_

/**
 * @brief
 *
 * @details
 *
 * @tparam containert
 * @param old_container
 * @param new_container
 * @param it
 * @return
 */
template<class containert>
typename containert::iterator copy_iterator(
    const containert &old_container,
    containert &new_container,
    typename containert::const_iterator it);

/**
 * @brief
 *
 * @details
 *
 * @tparam containert
 * @tparam iterator_containert
 * @param old_container
 * @param new_container
 * @param iterators
 * @return
 */
template<class containert, class iterator_containert>
iterator_containert copy_iterators(
    const containert &old_container,
    containert &new_container,
    const iterator_containert &iterators);

#include "iterator_helper.inc"

#endif /* CEGIS_UTIL_ITERATOR_HELPER_H_ */
