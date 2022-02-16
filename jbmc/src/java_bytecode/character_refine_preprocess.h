/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.
        For now support is limited to character in the ASCII range,
        some methods may have incorrect specifications outside of this range.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

/// \file
/// Preprocess a goto-programs so that calls to the java Character library are
///   replaced by simple expressions. For now support is limited to character in
///   the ASCII range, some methods may have incorrect specifications outside of
///   this range.

#ifndef CPROVER_JAVA_BYTECODE_CHARACTER_REFINE_PREPROCESS_H
#define CPROVER_JAVA_BYTECODE_CHARACTER_REFINE_PREPROCESS_H

#include <goto-programs/goto_instruction_code.h>

#include <util/mp_arith.h>
#include <util/std_code.h>

#include <unordered_map>

class character_refine_preprocesst
{
public:
  void initialize_conversion_table();
  codet replace_character_call(const code_function_callt &call) const;

private:
  typedef const code_function_callt &conversion_inputt;
  typedef codet (*conversion_functiont)(conversion_inputt &target);
  // A table tells us what method to call for each java method signature
  std::unordered_map<irep_idt, conversion_functiont> conversion_table;

  // Conversion functions
  static exprt expr_of_char_count(const exprt &chr, const typet &type);
  static codet convert_char_count(conversion_inputt &target);
  static exprt expr_of_char_value(const exprt &chr, const typet &type);
  static codet convert_char_value(conversion_inputt &target);
  static codet convert_compare(conversion_inputt &target);
  static codet convert_digit_char(conversion_inputt &target);
  static codet convert_digit_int(conversion_inputt &target);
  static codet convert_for_digit(conversion_inputt &target);
  static codet convert_get_directionality_char(conversion_inputt &target);
  static codet convert_get_directionality_int(conversion_inputt &target);
  static codet convert_get_numeric_value_char(conversion_inputt &target);
  static codet convert_get_numeric_value_int(conversion_inputt &target);
  static codet convert_get_type_char(conversion_inputt &target);
  static codet convert_get_type_int(conversion_inputt &target);
  static codet convert_hash_code(conversion_inputt &target);
  static exprt expr_of_high_surrogate(const exprt &chr, const typet &type);
  static codet convert_high_surrogate(conversion_inputt &target);
  static exprt expr_of_is_alphabetic(const exprt &chr, const typet &type);
  static codet convert_is_alphabetic(conversion_inputt &target);
  static exprt expr_of_is_bmp_code_point(const exprt &chr, const typet &type);
  static codet convert_is_bmp_code_point(conversion_inputt &target);
  static exprt expr_of_is_defined(const exprt &chr, const typet &type);
  static codet convert_is_defined_char(conversion_inputt &target);
  static codet convert_is_defined_int(conversion_inputt &target);
  static exprt expr_of_is_digit(const exprt &chr, const typet &type);
  static codet convert_is_digit_char(conversion_inputt &target);
  static codet convert_is_digit_int(conversion_inputt &target);
  static exprt expr_of_is_high_surrogate(const exprt &chr, const typet &type);
  static codet convert_is_high_surrogate(conversion_inputt &target);
  static exprt expr_of_is_identifier_ignorable(
    const exprt &chr, const typet &type);
  static codet convert_is_identifier_ignorable_char(conversion_inputt &target);
  static codet convert_is_identifier_ignorable_int(conversion_inputt &target);
  static codet convert_is_ideographic(conversion_inputt &target);
  static codet convert_is_ISO_control_char(conversion_inputt &target);
  static codet convert_is_ISO_control_int(conversion_inputt &target);
  static codet convert_is_java_identifier_part_char(conversion_inputt &target);
  static codet convert_is_java_identifier_part_int(conversion_inputt &target);
  static codet convert_is_java_identifier_start_char(conversion_inputt &target);
  static codet convert_is_java_identifier_start_int(conversion_inputt &target);
  static codet convert_is_java_letter(conversion_inputt &target);
  static codet convert_is_java_letter_or_digit(conversion_inputt &target);
  static exprt expr_of_is_letter(const exprt &chr, const typet &type);
  static codet convert_is_letter_char(conversion_inputt &target);
  static codet convert_is_letter_int(conversion_inputt &target);
  static exprt expr_of_is_letter_or_digit(const exprt &chr, const typet &type);
  static codet convert_is_letter_or_digit_char(conversion_inputt &target);
  static codet convert_is_letter_or_digit_int(conversion_inputt &target);
  static exprt expr_of_is_ascii_lower_case(const exprt &chr, const typet &type);
  static codet convert_is_lower_case_char(conversion_inputt &target);
  static codet convert_is_lower_case_int(conversion_inputt &target);
  static codet convert_is_low_surrogate(conversion_inputt &target);
  static exprt expr_of_is_mirrored(const exprt &chr, const typet &type);
  static codet convert_is_mirrored_char(conversion_inputt &target);
  static codet convert_is_mirrored_int(conversion_inputt &target);
  static codet convert_is_space(conversion_inputt &target);
  static exprt expr_of_is_space_char(const exprt &chr, const typet &type);
  static codet convert_is_space_char(conversion_inputt &target);
  static codet convert_is_space_char_int(conversion_inputt &target);
  static exprt expr_of_is_supplementary_code_point(
    const exprt &chr, const typet &type);
  static codet convert_is_supplementary_code_point(conversion_inputt &target);
  static exprt expr_of_is_surrogate(const exprt &chr, const typet &type);
  static codet convert_is_surrogate(conversion_inputt &target);
  static codet convert_is_surrogate_pair(conversion_inputt &target);
  static exprt expr_of_is_title_case(const exprt &chr, const typet &type);
  static codet convert_is_title_case_char(conversion_inputt &target);
  static codet convert_is_title_case_int(conversion_inputt &target);
  static exprt expr_of_is_letter_number(const exprt &chr, const typet &type);
  static exprt expr_of_is_unicode_identifier_part(
    const exprt &chr, const typet &type);
  static codet convert_is_unicode_identifier_part_char(
    conversion_inputt &target);
  static codet convert_is_unicode_identifier_part_int(
    conversion_inputt &target);
  static exprt expr_of_is_unicode_identifier_start(
    const exprt &chr, const typet &type);
  static codet convert_is_unicode_identifier_start_char(
    conversion_inputt &target);
  static codet convert_is_unicode_identifier_start_int(
    conversion_inputt &target);
  static exprt expr_of_is_ascii_upper_case(const exprt &chr, const typet &type);
  static codet convert_is_upper_case_char(conversion_inputt &target);
  static codet convert_is_upper_case_int(conversion_inputt &target);
  static exprt expr_of_is_valid_code_point(const exprt &chr, const typet &type);
  static codet convert_is_valid_code_point(conversion_inputt &target);
  static exprt expr_of_is_whitespace(const exprt &chr, const typet &type);
  static codet convert_is_whitespace_char(conversion_inputt &target);
  static codet convert_is_whitespace_int(conversion_inputt &target);
  static exprt expr_of_low_surrogate(const exprt &chr, const typet &type);
  static codet convert_low_surrogate(conversion_inputt &target);
  static exprt expr_of_reverse_bytes(const exprt &chr, const typet &type);
  static codet convert_reverse_bytes(conversion_inputt &target);
  static exprt expr_of_to_chars(const exprt &chr, const typet &type);
  static codet convert_to_chars(conversion_inputt &target);
  static exprt expr_of_to_lower_case(const exprt &chr, const typet &type);
  static codet convert_to_lower_case_char(conversion_inputt &target);
  static codet convert_to_lower_case_int(conversion_inputt &target);
  static exprt expr_of_to_title_case(const exprt &chr, const typet &type);
  static codet convert_to_title_case_char(conversion_inputt &target);
  static codet convert_to_title_case_int(conversion_inputt &target);
  static exprt expr_of_to_upper_case(const exprt &chr, const typet &type);
  static codet convert_to_upper_case_char(conversion_inputt &target);
  static codet convert_to_upper_case_int(conversion_inputt &target);

  // Helper functions
  static codet convert_char_function(
    exprt (*expr_function)(const exprt &chr, const typet &type),
    conversion_inputt &target);
  static exprt in_interval_expr(
    const exprt &chr,
    const mp_integer &lower_bound,
    const mp_integer &upper_bound);
  static exprt in_list_expr(
    const exprt &chr, const std::list<mp_integer> &list);
};

#endif // CPROVER_JAVA_BYTECODE_CHARACTER_REFINE_PREPROCESS_H
