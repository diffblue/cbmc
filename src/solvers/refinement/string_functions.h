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
bool is_string_length_func(irep_idt id);
bool is_string_equal_func(irep_idt id);
bool is_string_char_at_func(irep_idt id);
bool is_string_concat_func(irep_idt id);
bool is_string_substring_func(irep_idt id);
bool is_string_is_prefix_func(irep_idt id);
bool is_string_is_suffix_func(irep_idt id);
bool is_string_startswith_func(irep_idt id);
bool is_string_endswith_func(irep_idt id);
bool is_string_contains_func(irep_idt id);
bool is_string_char_set_func(irep_idt id);
bool is_string_index_of_func(irep_idt id);
bool is_string_last_index_of_func(irep_idt id);
bool is_string_copy_func(irep_idt id);


#endif
