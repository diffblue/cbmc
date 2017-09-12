/*******************************************************************\

Module: Hack for C string tests

Author: Romain Brenguier

\*******************************************************************/

#ifndef CPROVER_ESSION_STRINGS_CPROVER_STRING_HACK_H
#define CPROVER_ESSION_STRINGS_CPROVER_STRING_HACK_H

typedef struct __attribute__((__packed__)) __CPROVER_refined_string_type // NOLINT
  { int length; char content[]; } __CPROVER_refined_string_type;
typedef __CPROVER_refined_string_type __CPROVER_string;                  //NOLINT

/******************************************************************************
 * CPROVER string functions
 ******************************************************************************/
/* returns s[p] */
#define __CPROVER_char_at(s, p) \
  __CPROVER_uninterpreted_string_char_at_func(s, p)

/* string equality */
#define __CPROVER_string_equal(s1, s2) \
  __CPROVER_uninterpreted_string_equal_func(s1, s2)

/* defines a string literal, e.g. __CPROVER_string_literal("foo") */
#define __CPROVER_string_literal(s) \
  __CPROVER_uninterpreted_string_literal_func(s)

/* defines a char literal, e.g. __CPROVER_char_literal("c"). NOTE: you
 * *must* use a C string literal as argument (i.e. double quotes "c", not
 * single 'c') */
#define __CPROVER_char_literal(c) __CPROVER_uninterpreted_char_literal_func(c)

/* produces the concatenation of s1 and s2 */
#define __CPROVER_string_concat(s1, s2) \
  __CPROVER_uninterpreted_string_concat_func(s1, s2)

/* return the length of s */
#define __CPROVER_string_length(s) \
  __CPROVER_uninterpreted_string_length_func(s)

/* extracts the substring between positions i and j (j not included) */
#define __CPROVER_string_substring(s, i, j) \
  __CPROVER_uninterpreted_string_substring_func(s, i, j)

/* test whether p is a prefix of s */
#define __CPROVER_string_isprefix(p, s) \
  __CPROVER_uninterpreted_string_is_prefix_func(p, s)

/* test whether p is a suffix of s */
#define __CPROVER_string_issuffix(p, s) \
  __CPROVER_uninterpreted_string_is_suffix_func(p, s)
/* test whether p contains s */
#define __CPROVER_string_contains(p, s) \
  __CPROVER_uninterpreted_string_contains_func(p, s)

/* first index where character c appears, -1 if not found */
#define __CPROVER_string_index_of(s, c) \
  __CPROVER_uninterpreted_string_index_of_func(s, c)

/* last index where character c appears */
#define __CPROVER_string_last_index_of(s, c) \
  __CPROVER_uninterpreted_string_last_index_of_func(s, c)

/* returns a new string obtained from s by setting s[p] = c */
#define __CPROVER_char_set(s, p, c) \
  __CPROVER_uninterpreted_string_char_set_func(s, p, c)


#define __CPROVER_string_copy(s) __CPROVER_uninterpreted_string_copy_func(s)
#define __CPROVER_parse_int(s) __CPROVER_uninterpreted_string_parse_int_func(s)
#define __CPROVER_string_of_int(i) __CPROVER_uninterpreted_string_of_int_func(i)


/******************************************************************************
 * don't use these directly
 ******************************************************************************/
extern char __CPROVER_uninterpreted_string_char_at_func(
  __CPROVER_string str, int pos);
extern __CPROVER_bool __CPROVER_uninterpreted_string_equal_func(
  __CPROVER_string str1, __CPROVER_string str2);
extern __CPROVER_string __CPROVER_uninterpreted_string_literal_func(char * str);
extern char __CPROVER_uninterpreted_char_literal_func();
extern __CPROVER_string __CPROVER_uninterpreted_string_concat_func(
  __CPROVER_string str1, __CPROVER_string str2);
extern int __CPROVER_uninterpreted_string_length_func(__CPROVER_string str);
extern __CPROVER_string __CPROVER_uninterpreted_string_substring_func(
  __CPROVER_string str, int i, int j);
extern __CPROVER_bool __CPROVER_uninterpreted_string_is_prefix_func(
  __CPROVER_string pref, __CPROVER_string str);
extern __CPROVER_bool __CPROVER_uninterpreted_string_is_suffix_func(
  __CPROVER_string suff, __CPROVER_string str);
extern __CPROVER_bool __CPROVER_uninterpreted_string_contains_func(
  __CPROVER_string str1, __CPROVER_string str2);
extern int __CPROVER_uninterpreted_string_index_of_func(
  __CPROVER_string str, char c);
extern int __CPROVER_uninterpreted_string_last_index_of_func(
  __CPROVER_string str, char c);
extern __CPROVER_string __CPROVER_uninterpreted_string_char_set_func(
  __CPROVER_string str, int pos, char c);
extern __CPROVER_string __CPROVER_uninterpreted_string_copy_func(
  __CPROVER_string str);
extern int __CPROVER_uninterpreted_string_parse_int_func(__CPROVER_string str);
extern __CPROVER_string __CPROVER_uninterpreted_string_of_int_func(int i);

#endif
