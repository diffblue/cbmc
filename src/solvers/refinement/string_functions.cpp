/*******************************************************************\

Module: Defines identifiers for string functions

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/
#include <solvers/refinement/string_functions.h>


#define char_literal_func "__CPROVER_uninterpreted_char_literal"
#define string_length_func "__CPROVER_uninterpreted_strlen"
#define string_equal_func "__CPROVER_uninterpreted_string_equal"
#define string_char_at_func "__CPROVER_uninterpreted_char_at"
#define string_concat_func "__CPROVER_uninterpreted_strcat"
#define string_substring_func "__CPROVER_uninterpreted_substring"
#define string_is_prefix_func "__CPROVER_uninterpreted_strprefixof"
#define string_is_suffix_func "__CPROVER_uninterpreted_strsuffixof"
#define string_contains_func "__CPROVER_uninterpreted_strcontains"
#define string_char_set_func "__CPROVER_uninterpreted_char_set"
#define string_index_of_func "__CPROVER_uninterpreted_strindexof"
#define string_last_index_of_func "__CPROVER_uninterpreted_strlastindexof"
#define string_literal_func "__CPROVER_uninterpreted_string_literal"

bool starts_with(std::string s, std::string t) {
  for(int i = 0; i < t.length(); i++)
    if(s[i] != t[i]) return false;
  return true;
}

bool is_string_literal_func(irep_idt id) {
  return (starts_with(id2string(id),string_literal_func));
}

bool is_char_literal_func(irep_idt id) {
  return (starts_with(id2string(id),char_literal_func));
}
bool is_string_length_func(irep_idt id) {
  return (starts_with(id2string(id),string_length_func));
}
bool is_string_equal_func(irep_idt id) {
  return (starts_with(id2string(id),string_equal_func));
}
bool is_string_char_at_func(irep_idt id) {
  return (starts_with(id2string(id),string_char_at_func));
}
bool is_string_concat_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_func));
}
bool is_string_substring_func(irep_idt id) {
  return (starts_with(id2string(id),string_substring_func));
}
bool is_string_is_prefix_func(irep_idt id) {
  return (starts_with(id2string(id),string_is_prefix_func));
}
bool is_string_is_suffix_func(irep_idt id) {
  return (starts_with(id2string(id),string_is_suffix_func));
}
bool is_string_contains_func(irep_idt id) {
  return (starts_with(id2string(id),string_contains_func));
}
bool is_string_char_set_func(irep_idt id) {
  return (starts_with(id2string(id),string_char_set_func));
}
bool is_string_index_of_func(irep_idt id) {
  return (starts_with(id2string(id),string_index_of_func));
}
bool is_string_last_index_of_func(irep_idt id) {
  return (starts_with(id2string(id),string_last_index_of_func));
}

