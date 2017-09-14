// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Useful functions for manipulating/inspecting types.

#ifndef CPROVER_UTIL_TYPE_TRAITS_H
#define CPROVER_UTIL_TYPE_TRAITS_H


// Utility to check whether a value type or the referand
// of a reference or pointer is const.
template<typename T> struct is_referand_const:std::false_type {};
template<typename T> struct is_referand_const<const T &>:std::true_type {};
template<typename T> struct is_referand_const<const T &&>:std::true_type {};
template<typename T> struct is_referand_const<const T *>:std::true_type {};
template<typename T> struct is_referand_const<const T *const>:std::true_type {};
template<typename T> struct is_referand_const<const T>:std::true_type {};


// Utility to add const to a value type or the referand
// of a reference or pointer, if it isn't already.
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const { typedef const T type; };
// Specialisation for const l-value reference
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<const T &> { typedef const T &type; };
// Specialisation for l-value reference
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<T &> { typedef const T &type; };
// Specialisation for const r-value reference
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<const T &&> { typedef const T &&type; };
// Specialisation for r-value reference
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<T &&> { typedef const T &&type; };
// Specialisation for pointer to const
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<const T *> { typedef const T * type; };
// Specialisation for pointer
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<T *> { typedef const T * type; };
// Specialisation for const pointer to const
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<const T * const> { typedef const T * const type; };
// Specialisation for const pointer
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<T * const> { typedef const T * const type; };
// Specialisation for const object
template<typename T>
// NOLINTNEXTLINE(readability/identifiers)  - this is a function
struct make_referand_const<const T> { typedef const T type; };


template<bool make_const, typename BaseType>
// NOLINTNEXTLINE(readability/namespace)  - can't template typedefs
using conditionally_make_referand_const=
  typename std::conditional<
    make_const,
    typename make_referand_const<BaseType>::type,
    BaseType>::type;

#endif
