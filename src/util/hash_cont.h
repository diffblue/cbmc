/*******************************************************************\

Module: STL Hash map / set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HASH_CONT_H
#define CPROVER_HASH_CONT_H

// you need to pick one of the following three options

// #define STL_HASH_NONE
// #define STL_HASH_STDEXT
// #define STL_HASH_GNU
// #define STL_HASH_TR1

#if defined(STL_HASH_NONE)

#include <map>
#include <set>

template<class T1, class T2, class T3>
typedef std::map<T1, T2> hash_map_cont;

template<class T1, class T2>
typedef std::set<T1> hash_set_cont;

template<class T1, class T2>
typedef std::multiset<T1> hash_multiset_cont;

#elif defined(STL_HASH_STDEXT)

#include <hash_map>
#include <hash_set>

// for Visual Studio >= 2003

#define hash_map_cont stdext::hash_map
#define hash_set_cont stdext::hash_set
#define hash_multiset_cont stdext::hash_multiset

#elif defined(STL_HASH_GNU)

#include <ext/hash_map>
#include <ext/hash_set>

// for new g++ libraries >= 3.2

#define hash_map_cont __gnu_cxx::hash_map
#define hash_set_cont __gnu_cxx::hash_set
#define hash_multiset_cont __gnu_cxx::hash_multiset

#elif defined(STL_HASH_TR1)

#ifdef _MSC_VER
#include <unordered_set>
#include <unordered_map>
#else
#include <tr1/unordered_set>
#include <tr1/unordered_map>
#endif

#define hash_map_cont std::tr1::unordered_map
#define hash_set_cont std::tr1::unordered_set
#define hash_multiset_cont std::tr1::unordered_multiset

#else

#error Please select hash container option

#endif

#endif
