/*******************************************************************\

Module: Defines identifiers for string functions

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/
#include <solvers/refinement/string_functions.h>


#define char_literal_func "__CPROVER_uninterpreted_char_literal"
#define string_length_func "__CPROVER_uninterpreted_strlen"
#define string_equal_func "__CPROVER_uninterpreted_string_equal_func"
#define string_char_at_func "__CPROVER_uninterpreted_char_at"
#define string_concat_func "__CPROVER_uninterpreted_strcat_func"
#define string_concat_int_func "__CPROVER_uninterpreted_strcat_int_func"
#define string_concat_long_func "__CPROVER_uninterpreted_strcat_long_func"
#define string_concat_char_func "__CPROVER_uninterpreted_strcat_char_func"
#define string_concat_bool_func "__CPROVER_uninterpreted_strcat_bool_func"
#define string_concat_float_func "__CPROVER_uninterpreted_strcat_float_func"
#define string_concat_double_func "__CPROVER_uninterpreted_strcat_double_func"
#define string_substring_func "__CPROVER_uninterpreted_substring"
#define string_is_prefix_func "__CPROVER_uninterpreted_strprefixof"
#define string_is_suffix_func "__CPROVER_uninterpreted_strsuffixof"
#define string_endswith_func "__CPROVER_uninterpreted_string_endswith"
#define string_startswith_func "__CPROVER_uninterpreted_string_startswith"
#define string_contains_func "__CPROVER_uninterpreted_strcontains"
#define string_char_set_func "__CPROVER_uninterpreted_char_set"
#define string_index_of_func "__CPROVER_uninterpreted_strindexof"
#define string_last_index_of_func "__CPROVER_uninterpreted_strlastindexof"
#define string_literal_func "__CPROVER_uninterpreted_string_literal"
#define string_copy_func "__CPROVER_uninterpreted_string_copy"
#define string_empty_string_func "__CPROVER_uninterpreted_empty_string"
#define string_parse_int_func "__CPROVER_uninterpreted_parse_int"
#define string_of_int_func "__CPROVER_uninterpreted_string_of_int"
#define string_of_long_func "__CPROVER_uninterpreted_string_of_long"
#define string_of_bool_func "__CPROVER_uninterpreted_string_of_bool"
#define string_of_float_func "__CPROVER_uninterpreted_string_of_float"
#define string_of_double_func "__CPROVER_uninterpreted_string_of_double"
#define string_equals_ignore_case_func "__CPROVER_uninterpreted_string_equals_ignore_case"
#define string_trim_func "__CPROVER_uninterpreted_string_trim"
#define string_to_lower_case_func "__CPROVER_uninterpreted_string_to_lower_case"
#define string_to_upper_case_func "__CPROVER_uninterpreted_string_to_upper_case"
#define string_is_empty_func "__CPROVER_uninterpreted_string_is_empty"
#define string_value_of_func "__CPROVER_uninterpreted_string_value_of"
#define string_set_length_func "__CPROVER_uninterpreted_string_set_length"


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
bool is_string_concat_int_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_int_func));
}
bool is_string_concat_long_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_long_func));
}
bool is_string_concat_char_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_char_func));
}
bool is_string_concat_bool_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_bool_func));
}
bool is_string_concat_float_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_float_func));
}
bool is_string_concat_double_func(irep_idt id) {
  return (starts_with(id2string(id),string_concat_double_func));
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
bool is_string_startswith_func(irep_idt id) {
  return (starts_with(id2string(id),string_startswith_func));
}
bool is_string_endswith_func(irep_idt id) {
  return (starts_with(id2string(id),string_endswith_func));
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
bool is_string_copy_func(irep_idt id) {
  return (starts_with(id2string(id),string_copy_func));
}
bool is_string_last_index_of_func(irep_idt id) {
  return (starts_with(id2string(id),string_last_index_of_func));
}
bool is_string_empty_string_func(irep_idt id) {
  return (starts_with(id2string(id),string_empty_string_func));
}
bool is_string_parse_int_func(irep_idt id) {
  return (starts_with(id2string(id),string_parse_int_func));
}
bool is_string_of_int_func(irep_idt id) {
  return (starts_with(id2string(id),string_of_int_func));
}
bool is_string_of_long_func(irep_idt id) {
  return (starts_with(id2string(id),string_of_int_func));
}
bool is_string_of_bool_func(irep_idt id){
  return (starts_with(id2string(id),string_of_bool_func));
}
bool is_string_of_float_func(irep_idt id){
  return (starts_with(id2string(id),string_of_float_func));
}
bool is_string_of_double_func(irep_idt id){
  return (starts_with(id2string(id),string_of_double_func));
}
bool is_string_equals_ignore_case_func(irep_idt id){
  return (starts_with(id2string(id),string_equals_ignore_case_func));
}
bool is_string_trim_func(irep_idt id){
  return (starts_with(id2string(id),string_trim_func));
}
bool is_string_to_lower_case_func(irep_idt id){
  return (starts_with(id2string(id),string_to_lower_case_func));
}
bool is_string_to_upper_case_func(irep_idt id){
  return (starts_with(id2string(id),string_to_upper_case_func));
}
bool is_string_is_empty_func(irep_idt id){
  return (starts_with(id2string(id),string_is_empty_func));
}
bool is_string_value_of_func(irep_idt id){
  return (starts_with(id2string(id),string_value_of_func));
}
bool is_string_set_length_func(irep_idt id){
  return (starts_with(id2string(id),string_set_length_func));
}


