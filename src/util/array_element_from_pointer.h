/*******************************************************************\

Module: Element access in a pointer array

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_ARRAY_ELEMENT_FROM_POINTER_H
#define CPROVER_UTIL_ARRAY_ELEMENT_FROM_POINTER_H

#include "std_expr.h"

/// Generate statement using pointer arithmetic to access the element at the
/// given index of a pointer array:
/// `*(pointer + index)`
/// Arrays are sometimes (always in JBMC) represented as a pointer to their
/// first element, especially when their length in uncertain, as the length is
/// part of any array type. But we know the type of the first element of the
/// array, so we work with that instead.
/// \param pointer: pointer to the first element of an array
/// \param index: index of the element to access
/// \return expression representing the (\p index)'th element of the array
dereference_exprt
array_element_from_pointer(const exprt &pointer, const exprt &index);

#endif // CPROVER_UTIL_ARRAY_ELEMENT_FROM_POINTER_H
