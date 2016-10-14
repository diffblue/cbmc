/*******************************************************************\

Module: Defines identifiers for string functions

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_STRING_FUNCTIONS_H
#define CPROVER_STRING_FUNCTIONS_H

#include <util/irep.h>

bool starts_with(irep_idt id, irep_idt prefix);
const irep_idt cprover_char_literal_func("__CPROVER_uninterpreted_char_literal_func");
const irep_idt cprover_string_literal_func("__CPROVER_uninterpreted_string_literal_func");
const irep_idt cprover_string_char_at_func("__CPROVER_uninterpreted_string_char_at_func");
const irep_idt cprover_string_char_set_func("__CPROVER_uninterpreted_string_char_set_func");
const irep_idt cprover_string_code_point_at_func("__CPROVER_uninterpreted_string_code_point_at_func");
const irep_idt cprover_string_code_point_before_func("__CPROVER_uninterpreted_string_code_point_before_func");
const irep_idt cprover_string_code_point_count_func("__CPROVER_uninterpreted_string_code_point_count_func");
const irep_idt cprover_string_offset_by_code_point_func("__CPROVER_uninterpreted_string_offset_by_code_point_func");
const irep_idt cprover_string_compare_to_func("__CPROVER_uninterpreted_string_compare_to_func");
const irep_idt cprover_string_concat_func("__CPROVER_uninterpreted_string_concat_func");
const irep_idt cprover_string_concat_int_func("__CPROVER_uninterpreted_string_concat_int_func");
const irep_idt cprover_string_concat_long_func("__CPROVER_uninterpreted_string_concat_long_func");
const irep_idt cprover_string_concat_char_func("__CPROVER_uninterpreted_string_concat_char_func");
const irep_idt cprover_string_concat_bool_func("__CPROVER_uninterpreted_string_concat_bool_func");
const irep_idt cprover_string_concat_double_func("__CPROVER_uninterpreted_string_concat_double_func");
const irep_idt cprover_string_concat_float_func("__CPROVER_uninterpreted_string_concat_float_func");
const irep_idt cprover_string_concat_code_point_func("__CPROVER_uninterpreted_string_concat_code_point_func");
const irep_idt cprover_string_contains_func("__CPROVER_uninterpreted_string_contains_func");
const irep_idt cprover_string_copy_func("__CPROVER_uninterpreted_string_copy_func");
const irep_idt cprover_string_delete_func("__CPROVER_uninterpreted_string_delete_func");
const irep_idt cprover_string_delete_char_at_func("__CPROVER_uninterpreted_string_delete_char_at_func");
const irep_idt cprover_string_equal_func("__CPROVER_uninterpreted_string_equal_func");
const irep_idt cprover_string_equals_ignore_case_func("__CPROVER_uninterpreted_string_equals_ignore_case_func");
const irep_idt cprover_string_empty_string_func("__CPROVER_uninterpreted_string_empty_string_func");
const irep_idt cprover_string_endswith_func("__CPROVER_uninterpreted_string_endswith_func");
const irep_idt cprover_string_format_func("__CPROVER_uninterpreted_string_format_func");
const irep_idt cprover_string_hash_code_func("__CPROVER_uninterpreted_string_hash_code_func");
const irep_idt cprover_string_index_of_func("__CPROVER_uninterpreted_string_index_of_func");
const irep_idt cprover_string_intern_func("__CPROVER_uninterpreted_string_intern_func");
const irep_idt cprover_string_insert_func("__CPROVER_uninterpreted_string_insert_func");
const irep_idt cprover_string_insert_int_func("__CPROVER_uninterpreted_string_insert_int_func");
const irep_idt cprover_string_insert_long_func("__CPROVER_uninterpreted_string_insert_long_func");
const irep_idt cprover_string_insert_bool_func("__CPROVER_uninterpreted_string_insert_bool_func");
const irep_idt cprover_string_insert_char_func("__CPROVER_uninterpreted_string_insert_char_func");
const irep_idt cprover_string_insert_float_func("__CPROVER_uninterpreted_string_insert_float_func");
const irep_idt cprover_string_insert_double_func("__CPROVER_uninterpreted_string_insert_double_func");
const irep_idt cprover_string_is_prefix_func("__CPROVER_uninterpreted_string_is_prefix_func");
const irep_idt cprover_string_is_suffix_func("__CPROVER_uninterpreted_string_is_suffix_func");
const irep_idt cprover_string_is_empty_func("__CPROVER_uninterpreted_string_is_empty_func");
const irep_idt cprover_string_last_index_of_func("__CPROVER_uninterpreted_string_last_index_of_func");
const irep_idt cprover_string_length_func("__CPROVER_uninterpreted_string_length_func");
const irep_idt cprover_string_of_int_func("__CPROVER_uninterpreted_string_of_int_func");
const irep_idt cprover_string_of_int_hex_func("__CPROVER_uninterpreted_string_of_int_hex_func");
const irep_idt cprover_string_of_long_func("__CPROVER_uninterpreted_string_of_long_func");
const irep_idt cprover_string_of_bool_func("__CPROVER_uninterpreted_string_of_bool_func");
const irep_idt cprover_string_of_float_func("__CPROVER_uninterpreted_string_of_float_func");
const irep_idt cprover_string_of_double_func("__CPROVER_uninterpreted_string_of_double_func");
const irep_idt cprover_string_of_char_func("__CPROVER_uninterpreted_string_of_char_func");
const irep_idt cprover_string_parse_int_func("__CPROVER_uninterpreted_string_parse_int_func");
const irep_idt cprover_string_replace_func("__CPROVER_uninterpreted_string_replace_func");
const irep_idt cprover_string_set_length_func("__CPROVER_uninterpreted_string_set_length_func");
const irep_idt cprover_string_startswith_func("__CPROVER_uninterpreted_string_startswith_func");
const irep_idt cprover_string_substring_func("__CPROVER_uninterpreted_string_substring_func");
const irep_idt cprover_string_to_char_array_func("__CPROVER_uninterpreted_string_to_char_array_func");
const irep_idt cprover_string_to_lower_case_func("__CPROVER_uninterpreted_string_to_lower_case_func");
const irep_idt cprover_string_to_upper_case_func("__CPROVER_uninterpreted_string_to_upper_case_func");
const irep_idt cprover_string_trim_func("__CPROVER_uninterpreted_string_trim_func");
const irep_idt cprover_string_value_of_func("__CPROVER_uninterpreted_string_value_of_func");

#endif
