/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_EXPR2C_CLASS_H
#define CPROVER_ANSI_C_EXPR2C_CLASS_H

#include "expr2c.h"

#include <string>
#include <unordered_map>
#include <unordered_set>

#include <goto-programs/goto_instruction_code.h>

#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/mathematical_expr.h>
#include <util/std_code.h>

class annotated_pointer_constant_exprt;
class qualifierst;
class namespacet;

class expr2ct
{
public:
  explicit expr2ct(
    const namespacet &_ns,
    const expr2c_configurationt &configuration =
      expr2c_configurationt::default_configuration)
    : ns(_ns), configuration(configuration), sizeof_nesting(0)
  {
  }
  virtual ~expr2ct() { }

  virtual std::string convert(const typet &src);
  virtual std::string convert(const exprt &src);

  void get_shorthands(const exprt &expr);

  std::string
  convert_with_identifier(const typet &src, const std::string &identifier);

protected:
  const namespacet &ns;
  const expr2c_configurationt &configuration;

  virtual std::string convert_rec(
    const typet &src,
    const qualifierst &qualifiers,
    const std::string &declarator);

  virtual std::string convert_struct_type(
    const typet &src,
    const std::string &qualifiers_str,
    const std::string &declarator_str);

  std::string convert_struct_type(
    const typet &src,
    const std::string &qualifer_str,
    const std::string &declarator_str,
    bool inc_struct_body,
    bool inc_padding_components);

  virtual std::string convert_array_type(
    const typet &src,
    const qualifierst &qualifiers,
    const std::string &declarator_str);

  std::string convert_array_type(
    const typet &src,
    const qualifierst &qualifiers,
    const std::string &declarator_str,
    bool inc_size_if_possible);

  static std::string indent_str(unsigned indent);

  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> ns_collision;
  std::unordered_map<irep_idt, irep_idt> shorthands;

  unsigned sizeof_nesting;

  irep_idt id_shorthand(const irep_idt &identifier) const;

  std::string convert_typecast(
    const typecast_exprt &src, unsigned &precedence);

  std::string convert_pointer_arithmetic(
    const exprt &src,
    unsigned &precedence);

  std::string convert_pointer_difference(
    const exprt &src,
    unsigned &precedence);

  std::string convert_binary(
    const binary_exprt &,
    const std::string &symbol,
    unsigned precedence,
    bool full_parentheses);

  std::string convert_multi_ary(
    const exprt &src, const std::string &symbol,
    unsigned precedence, bool full_parentheses);

  std::string convert_cond(
    const exprt &src, unsigned precedence);

  std::string convert_struct_member_value(
    const exprt &src, unsigned precedence);

  std::string convert_array_member_value(
    const exprt &src, unsigned precedence);

  std::string convert_member(
    const member_exprt &src, unsigned precedence);

  std::string convert_array_of(const exprt &src, unsigned precedence);

  std::string convert_trinary(
    const ternary_exprt &src,
    const std::string &symbol1,
    const std::string &symbol2,
    unsigned precedence);

  /// Conversion function from rol/ror expressions to C code strings
  /// Note that this constructs a complex expression to do bit
  /// twiddling since rol/ror operations are not native to ANSI-C.
  /// The complex expression is then recursively converted.
  /// \param src: is an exprt that must be either an rol or ror
  /// \param precedence: precedence for bracketing
  /// \returns string for performing rol/ror as bit twiddling with C
  std::string convert_rox(const shift_exprt &src, unsigned precedence);

  std::string convert_overflow(
    const exprt &src, unsigned &precedence);

  std::string convert_quantifier(
    const quantifier_exprt &,
    const std::string &symbol,
    unsigned precedence);

  std::string convert_with(
    const exprt &src, unsigned precedence);

  std::string convert_update(const update_exprt &, unsigned precedence);

  std::string convert_member_designator(
    const exprt &src);

  std::string convert_index_designator(
    const exprt &src);

  std::string convert_index(
    const exprt &src, unsigned precedence);

  std::string
  convert_byte_extract(const byte_extract_exprt &, unsigned precedence);

  std::string
  convert_byte_update(const byte_update_exprt &, unsigned precedence);

  std::string convert_extractbit(const extractbit_exprt &, unsigned precedence);

  std::string
  convert_extractbits(const extractbits_exprt &src, unsigned precedence);

  std::string convert_unary(
    const unary_exprt &,
    const std::string &symbol,
    unsigned precedence);

  std::string convert_unary_post(
    const exprt &src, const std::string &symbol,
    unsigned precedence);

  /// Returns a string if \p src is a function with a known conversion, else
  /// returns nullopt.
  optionalt<std::string> convert_function(const exprt &src);
  std::string convert_function(const exprt &src, const std::string &symbol);

  std::string convert_complex(
    const exprt &src,
    unsigned precedence);

  std::string convert_comma(
    const exprt &src,
    unsigned precedence);

  std::string convert_Hoare(const exprt &src);

  std::string convert_code(const codet &src);
  virtual std::string convert_code(const codet &src, unsigned indent);
  std::string convert_code_label(const code_labelt &src, unsigned indent);
  // NOLINTNEXTLINE(whitespace/line_length)
  std::string convert_code_switch_case(const code_switch_caset &src, unsigned indent);
  std::string convert_code_asm(const code_asmt &src, unsigned indent);
  std::string
  convert_code_frontend_assign(const code_frontend_assignt &, unsigned indent);
  // NOLINTNEXTLINE(whitespace/line_length)
  std::string convert_code_ifthenelse(const code_ifthenelset &src, unsigned indent);
  std::string convert_code_for(const code_fort &src, unsigned indent);
  std::string convert_code_while(const code_whilet &src, unsigned indent);
  std::string convert_code_dowhile(const code_dowhilet &src, unsigned indent);
  std::string convert_code_block(const code_blockt &src, unsigned indent);
  std::string convert_code_expression(const codet &src, unsigned indent);
  std::string convert_code_return(const codet &src, unsigned indent);
  std::string convert_code_goto(const codet &src, unsigned indent);
  std::string convert_code_assume(const codet &src, unsigned indent);
  std::string convert_code_assert(const codet &src, unsigned indent);
  std::string convert_code_break(unsigned indent);
  std::string convert_code_switch(const codet &src, unsigned indent);
  std::string convert_code_continue(unsigned indent);
  std::string convert_code_frontend_decl(const codet &, unsigned indent);
  std::string convert_code_decl_block(const codet &src, unsigned indent);
  std::string convert_code_dead(const codet &src, unsigned indent);
  // NOLINTNEXTLINE(whitespace/line_length)
  std::string convert_code_function_call(const code_function_callt &src, unsigned indent);
  std::string convert_code_lock(const codet &src, unsigned indent);
  std::string convert_code_unlock(const codet &src, unsigned indent);
  std::string convert_code_printf(const codet &src, unsigned indent);
  std::string convert_code_fence(const codet &src, unsigned indent);
  std::string convert_code_input(const codet &src, unsigned indent);
  std::string convert_code_output(const codet &src, unsigned indent);
  std::string convert_code_array_set(const codet &src, unsigned indent);
  std::string convert_code_array_copy(const codet &src, unsigned indent);
  std::string convert_code_array_replace(const codet &src, unsigned indent);

  virtual std::string convert_with_precedence(
    const exprt &src, unsigned &precedence);

  std::string
  convert_function_application(const function_application_exprt &src);
  std::string convert_side_effect_expr_function_call(
    const side_effect_expr_function_callt &src);
  std::string convert_allocate(const exprt &src, unsigned &precedence);
  std::string convert_nondet(const exprt &src, unsigned &precedence);
  std::string convert_prob_coin(const exprt &src, unsigned &precedence);
  std::string convert_prob_uniform(const exprt &src, unsigned &precedence);
  // NOLINTNEXTLINE(whitespace/line_length)
  std::string convert_statement_expression(const exprt &src, unsigned &precendence);

  virtual std::string convert_symbol(const exprt &src);
  std::string convert_predicate_symbol(const exprt &src);
  std::string convert_predicate_next_symbol(const exprt &src);
  std::string convert_predicate_passive_symbol(const exprt &src);
  std::string convert_nondet_symbol(const nondet_symbol_exprt &);
  std::string convert_quantified_symbol(const exprt &src);
  std::string convert_nondet_bool();
  std::string convert_object_descriptor(const exprt &src, unsigned &precedence);
  std::string convert_literal(const exprt &src);
  // NOLINTNEXTLINE(whitespace/line_length)
  virtual std::string convert_constant(const constant_exprt &src, unsigned &precedence);
  virtual std::string convert_constant_bool(bool boolean_value);
  virtual std::string convert_annotated_pointer_constant(
    const annotated_pointer_constant_exprt &src,
    unsigned &precedence);

  std::string convert_norep(const exprt &src, unsigned &precedence);

  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  std::string convert_union(const exprt &src, unsigned &precedence);
  std::string convert_vector(const exprt &src, unsigned &precedence);
  std::string convert_array(const exprt &src);
  std::string convert_array_list(const exprt &src, unsigned &precedence);
  std::string convert_initializer_list(const exprt &src);
  std::string convert_designated_initializer(const exprt &src);
  std::string convert_concatenation(const exprt &src, unsigned &precedence);
  std::string convert_sizeof(const exprt &src, unsigned &precedence);
  std::string convert_let(const let_exprt &, unsigned precedence);

  std::string convert_struct(
    const exprt &src,
    unsigned &precedence,
    bool include_padding_components);

  std::string convert_conditional_target_group(const exprt &src);
  std::string convert_bitreverse(const bitreverse_exprt &src);
};

#endif // CPROVER_ANSI_C_EXPR2C_CLASS_H
