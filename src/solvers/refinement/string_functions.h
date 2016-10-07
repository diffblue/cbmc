/*******************************************************************\

Module: Defines identifiers for string functions

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_STRING_FUNCTIONS_H
#define CPROVER_STRING_FUNCTIONS_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/string_constraint.h>

bool starts_with(std::string s, std::string t);
bool is_string_literal_func(irep_idt id);
bool is_char_literal_func(irep_idt id);
bool is_string_char_at_func(irep_idt id);
bool is_string_char_set_func(irep_idt id);
bool is_string_code_point_at_func(irep_idt id);
bool is_string_code_point_before_func(irep_idt id);
bool is_string_code_point_count_func(irep_idt id);
bool is_string_code_point_offset_by_code_point_func(irep_idt id);
bool is_string_concat_func(irep_idt id);
bool is_string_concat_int_func(irep_idt id);
bool is_string_concat_long_func(irep_idt id);
bool is_string_concat_char_func(irep_idt id);
bool is_string_concat_bool_func(irep_idt id);
bool is_string_concat_double_func(irep_idt id);
bool is_string_concat_float_func(irep_idt id);
bool is_string_contains_func(irep_idt id);
bool is_string_copy_func(irep_idt id);
bool is_string_delete_func(irep_idt id);
bool is_string_delete_char_at_func(irep_idt id);
bool is_string_equal_func(irep_idt id);
bool is_string_equals_ignore_case_func(irep_idt id);
bool is_string_empty_string_func(irep_idt id);
bool is_string_endswith_func(irep_idt id);
bool is_string_hash_code_func(irep_idt id);
bool is_string_index_of_func(irep_idt id);
bool is_string_insert_func(irep_idt id);
bool is_string_insert_int_func(irep_idt id);
bool is_string_insert_long_func(irep_idt id);
bool is_string_insert_bool_func(irep_idt id);
bool is_string_insert_char_func(irep_idt id);
bool is_string_insert_float_func(irep_idt id);
bool is_string_insert_double_func(irep_idt id);
bool is_string_is_prefix_func(irep_idt id);
bool is_string_is_suffix_func(irep_idt id);
bool is_string_is_empty_func(irep_idt id);
bool is_string_last_index_of_func(irep_idt id);
bool is_string_length_func(irep_idt id);
bool is_string_of_int_func(irep_idt id);
bool is_string_of_long_func(irep_idt id);
bool is_string_of_bool_func(irep_idt id);
bool is_string_of_float_func(irep_idt id);
bool is_string_of_double_func(irep_idt id);
bool is_string_of_char_func(irep_idt id);
bool is_string_parse_int_func(irep_idt id);
bool is_string_replace_func(irep_idt id);
bool is_string_set_length_func(irep_idt id);
bool is_string_startswith_func(irep_idt id);
bool is_string_substring_func(irep_idt id);
bool is_string_to_char_array_func(irep_idt id);
bool is_string_to_lower_case_func(irep_idt id);
bool is_string_to_upper_case_func(irep_idt id);
bool is_string_trim_func(irep_idt id);
bool is_string_value_of_func(irep_idt id);

#endif
