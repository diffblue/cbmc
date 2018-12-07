/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
#define CPROVER_SOLVERS_SMT2_SMT2_PARSER_H

#include <stack>

#include <util/std_expr.h>

#include "smt2_tokenizer.h"

class smt2_parsert:public smt2_tokenizert
{
public:
  explicit smt2_parsert(std::istream &_in)
    : smt2_tokenizert(_in), exit(false), parenthesis_level(0)
  {
  }

  bool parse() override
  {
    command_sequence();
    return false;
  }

  struct idt
  {
    idt():type(nil_typet())
    {
    }

    typet type;
    exprt definition;
    std::vector<irep_idt> parameters;
  };

  using id_mapt=std::map<irep_idt, idt>;
  id_mapt id_map;

  struct named_termt
  {
    exprt term;
    symbol_exprt name;
  };

  using named_termst = std::map<irep_idt, named_termt>;
  named_termst named_terms;

  bool exit;

  /// This skips tokens until all bracketed expressions are closed
  void skip_to_end_of_list();

protected:
  // we override next_token to track the parenthesis level
  std::size_t parenthesis_level;
  tokent next_token() override;

  void command_sequence();

  virtual void command(const std::string &);

  // for let/quantifier bindings, function parameters
  using renaming_mapt=std::map<irep_idt, irep_idt>;
  renaming_mapt renaming_map;
  using renaming_counterst=std::map<irep_idt, unsigned>;
  renaming_counterst renaming_counters;
  irep_idt get_fresh_id(const irep_idt &);
  irep_idt rename_id(const irep_idt &) const;

  struct signature_with_parameter_idst
  {
    typet type;
    std::vector<irep_idt> parameters;

    explicit signature_with_parameter_idst(const typet &_type) : type(_type)
    {
    }

    signature_with_parameter_idst(
      const typet &_type,
      const std::vector<irep_idt> &_parameters)
      : type(_type), parameters(_parameters)
    {
      PRECONDITION(
        (_type.id() == ID_mathematical_function &&
         to_mathematical_function_type(_type).domain().size() ==
           _parameters.size()) ||
        (_type.id() != ID_mathematical_function && _parameters.empty()));
    }
  };

  void ignore_command();
  exprt expression();
  exprt function_application();
  exprt function_application_ieee_float_op(
    const irep_idt &,
    const exprt::operandst &);
  exprt function_application_fp(const exprt::operandst &);
  typet sort();
  exprt::operandst operands();
  typet function_signature_declaration();
  signature_with_parameter_idst function_signature_definition();
  exprt multi_ary(irep_idt, const exprt::operandst &);
  exprt binary_predicate(irep_idt, const exprt::operandst &);
  exprt binary(irep_idt, const exprt::operandst &);
  exprt unary(irep_idt, const exprt::operandst &);

  exprt let_expression();
  exprt quantifier_expression(irep_idt);
  exprt function_application(
    const irep_idt &identifier,
    const exprt::operandst &op);

  /// Apply typecast to signedbv to expressions in vector
  exprt::operandst cast_bv_to_signed(const exprt::operandst &);

  /// Apply typecast to unsignedbv to given expression
  exprt cast_bv_to_unsigned(const exprt &);
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
