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
  explicit smt2_parsert(std::istream &_in):
    smt2_tokenizert(_in),
    exit(false)
  {
  }

  bool parse() override
  {
    command_sequence();
    return !ok;
  }

  struct idt
  {
    idt():type(nil_typet())
    {
    }

    typet type;
    exprt definition;
  };

  using id_mapt=std::map<irep_idt, idt>;
  id_mapt id_map;

protected:
  bool exit;
  void command_sequence();

  virtual void command(const std::string &);

  // for let/quantifier bindings, function parameters
  using renaming_mapt=std::map<irep_idt, irep_idt>;
  renaming_mapt renaming_map;
  using renaming_counterst=std::map<irep_idt, unsigned>;
  renaming_counterst renaming_counters;
  irep_idt get_fresh_id(const irep_idt &);
  irep_idt rename_id(const irep_idt &) const;

  void ignore_command();
  exprt expression();
  exprt function_application();
  typet sort();
  exprt::operandst operands();
  typet function_signature_declaration();
  typet function_signature_definition();
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
