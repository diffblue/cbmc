/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXPR2C_CLASS_H
#define CPROVER_EXPR2C_CLASS_H

#include <set>
#include <map>

#include <expr.h>
#include <std_code.h>
#include <std_expr.h>
#include <namespace.h>

#include "c_qualifiers.h"

class expr2ct
{
public:
  expr2ct(const namespacet &_ns):ns(_ns), sizeof_nesting(0) { }
  virtual ~expr2ct() { }

  virtual std::string convert(const typet &src);
  virtual std::string convert(const exprt &src);

  void get_shorthands(const exprt &expr);

protected:
  const namespacet &ns;

  virtual std::string convert_rec(
    const typet &src,
    const c_qualifierst &qualifiers,
    const std::string &declarator);

  static std::string indent_str(unsigned indent);

  std::set<exprt> symbols;
  std::map<irep_idt, exprt> shorthands;
  std::set<irep_idt> ns_collision;
  unsigned sizeof_nesting;

  void get_symbols(const exprt &expr);
  std::string id_shorthand(const exprt &expr) const;

  std::string convert_typecast(
    const typecast_exprt &src, unsigned &precedence);

  std::string convert_pointer_arithmetic(const exprt &src,
    unsigned &precedence);

  std::string convert_pointer_difference(const exprt &src,
    unsigned &precedence);

  std::string convert_implicit_address_of(
    const exprt &src, unsigned &precedence);

  std::string convert_binary(
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

  std::string convert_pointer_object_has_type(
    const exprt &src, unsigned precedence);

  std::string convert_array_of(const exprt &src, unsigned precedence);

  std::string convert_trinary(
    const exprt &src, const std::string &symbol1,
    const std::string &symbol2, unsigned precedence);

  std::string convert_overflow(
    const exprt &src, unsigned &precedence);

  std::string convert_quantifier(
    const exprt &src, const std::string &symbol,
    unsigned precedence);

  std::string convert_with(
    const exprt &src, unsigned precedence);

  std::string convert_update(
    const exprt &src, unsigned precedence);

  std::string convert_member_designator(
    const exprt &src);

  std::string convert_index_designator(
    const exprt &src);

  std::string convert_index(
    const exprt &src, unsigned precedence);

  std::string convert_byte_extract(
    const exprt &src,
    unsigned precedence);

  std::string convert_byte_update(
    const exprt &src,
    unsigned precedence);

  std::string convert_extractbit(
    const exprt &src,
    unsigned precedence);

  std::string convert_extractbits(
    const exprt &src,
    unsigned precedence);

  std::string convert_unary(
    const exprt &src, const std::string &symbol,
    unsigned precedence);

  std::string convert_unary_post(
    const exprt &src, const std::string &symbol,
    unsigned precedence);

  std::string convert_function(
    const exprt &src, const std::string &symbol,
    unsigned precedence);

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
  std::string convert_code_asm(const codet &src, unsigned indent);
  std::string convert_code_assign(const code_assignt &src, unsigned indent);
  std::string convert_code_free(const codet &src, unsigned indent);
  std::string convert_code_init(const codet &src, unsigned indent);
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
  std::string convert_code_break(const codet &src, unsigned indent);
  std::string convert_code_switch(const codet &src, unsigned indent);
  std::string convert_code_continue(const codet &src, unsigned indent);
  std::string convert_code_decl(const codet &src, unsigned indent);
  std::string convert_code_function_call(const code_function_callt &src, unsigned indent);
  std::string convert_code_lock(const codet &src, unsigned indent);
  std::string convert_code_unlock(const codet &src, unsigned indent);
  std::string convert_code_printf(const codet &src, unsigned indent);
  std::string convert_code_fence(const codet &src, unsigned indent);
  std::string convert_code_input(const codet &src, unsigned indent);
  std::string convert_code_array_set(const codet &src, unsigned indent);
  std::string convert_code_array_copy(const codet &src, unsigned indent);

  virtual std::string convert(const exprt &src, unsigned &precedence);

  std::string convert_function_application(const function_application_exprt &src, unsigned &precedence);
  std::string convert_side_effect_expr_function_call(const side_effect_expr_function_callt &src, unsigned &precedence);
  std::string convert_malloc(const exprt &src, unsigned &precedence);
  std::string convert_nondet(const exprt &src, unsigned &precedence);
  std::string convert_prob_coin(const exprt &src, unsigned &precedence);
  std::string convert_prob_uniform(const exprt &src, unsigned &precedence);
  std::string convert_statement_expression(const exprt &src, unsigned &precendence);

  virtual std::string convert_symbol(const exprt &src, unsigned &precedence);
  std::string convert_predicate_symbol(const exprt &src, unsigned &precedence);
  std::string convert_predicate_next_symbol(const exprt &src, unsigned &precedence);
  std::string convert_predicate_passive_symbol(const exprt &src, unsigned &precedence);
  std::string convert_nondet_symbol(const exprt &src, unsigned &precedence);
  std::string convert_quantified_symbol(const exprt &src, unsigned &precedence);
  std::string convert_nondet_bool(const exprt &src, unsigned &precedence);
  std::string convert_object_descriptor(const exprt &src, unsigned &precedence);
  std::string convert_literal(const exprt &src, unsigned &precedence);
  virtual std::string convert_constant(const exprt &src, unsigned &precedence);

  std::string convert_norep(const exprt &src, unsigned &precedence);

  virtual std::string convert_struct(const exprt &src, unsigned &precedence);
  std::string convert_union(const exprt &src, unsigned &precedence);
  std::string convert_vector(const exprt &src, unsigned &precedence);
  std::string convert_array(const exprt &src, unsigned &precedence);
  std::string convert_array_list(const exprt &src, unsigned &precedence);
  std::string convert_initializer_list(const exprt &src, unsigned &precedence);
  std::string convert_designated_initializer(const exprt &src, unsigned &precedence);
  std::string convert_concatenation(const exprt &src, unsigned &precedence);
};

#endif
