/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
#define CPROVER_SOLVERS_SMT2_SMT2_PARSER_H

#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include "smt2_tokenizer.h"

#include <map>
#include <optional>
#include <unordered_map>

class irept;

class smt2_parsert
{
public:
  explicit smt2_parsert(std::istream &_in)
    : exit(false), smt2_tokenizer(_in), parenthesis_level(0)
  {
    setup_commands();
    setup_sorts();
    setup_expressions();
  }

  void parse()
  {
    command_sequence();
  }

  struct idt
  {
    using kindt = enum { VARIABLE, BINDING, PARAMETER };

    idt(kindt _kind, const exprt &expr)
      : kind(_kind), type(expr.type()), definition(expr)
    {
    }

    idt(kindt _kind, typet __type)
      : kind(_kind), type(std::move(__type)), definition(nil_exprt())
    {
    }

    kindt kind;
    typet type;

    // this is a lambda when the symbol is a function
    exprt definition;
  };

  using id_mapt=std::map<irep_idt, idt>;
  id_mapt id_map;

  struct named_termt
  {
    /// Default-constructing a symbol_exprt is deprecated, thus make sure we
    /// always construct a named_termt from an initialized \p _name
    named_termt(const exprt &_term, const symbol_exprt &_name)
      : term(_term), name(_name)
    {
    }

    exprt term;
    symbol_exprt name;
  };

  using named_termst = std::map<irep_idt, named_termt>;
  named_termst named_terms;

  bool exit;

  smt2_tokenizert::smt2_errort error(const std::string &message) const
  {
    return smt2_tokenizer.error(message);
  }

  smt2_tokenizert::smt2_errort error() const
  {
    return smt2_tokenizer.error();
  }

  /// This skips tokens until all bracketed expressions are closed
  void skip_to_end_of_list();

protected:
  smt2_tokenizert smt2_tokenizer;
  // we extend next_token to track the parenthesis level
  std::size_t parenthesis_level;
  smt2_tokenizert::tokent next_token();

  // add the given identifier to the id_map but
  // complain if that identifier is used already
  void add_unique_id(irep_idt, exprt);

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

    // a convenience helper for iterating over identifiers and types
    std::vector<std::pair<irep_idt, typet>> ids_and_types() const
    {
      if(parameters.empty())
        return {};
      else
      {
        std::vector<std::pair<irep_idt, typet>> result;
        result.reserve(parameters.size());
        const auto &domain = to_mathematical_function_type(type).domain();
        for(std::size_t i = 0; i < parameters.size(); i++)
          result.emplace_back(parameters[i], domain[i]);
        return result;
      }
    }

    // convenience helper for constructing a binding
    binding_exprt::variablest binding_variables() const
    {
      binding_exprt::variablest result;
      for(auto &pair : ids_and_types())
        result.emplace_back(pair.first, pair.second);
      return result;
    }
  };

  // expressions
  std::unordered_map<std::string, std::function<exprt()>> expressions;
  void setup_expressions();
  exprt expression();
  exprt function_application();
  exprt function_application_with_id(const irep_idt &id);
  exprt function_application_ieee_float_op(
    const irep_idt &,
    const exprt::operandst &);
  exprt function_application_ieee_float_eq(const exprt::operandst &);
  exprt function_application_fp(const exprt::operandst &);
  exprt::operandst operands();

  /// When set, the next call to operands() takes these as its result rather
  /// than reading further from the tokenizer. Used by the iterative
  /// walker in convert_irep_to_exprt() to feed pre-computed operand
  /// exprts to the expressions[] / id_map dispatch logic in
  /// function_application_with_id().
  std::optional<exprt::operandst> precollected_operands;

  /// Convert a generic S-expression irept (as produced by smt2irep())
  /// into the corresponding exprt without using the C++ call stack for
  /// tree traversal: both operand collection and nested 'let' scoping are
  /// driven by an explicit work-list of frames. For simple function
  /// applications the existing tokenizer-based machinery is reused by
  /// dispatching through function_application_with_id() with
  /// precollected_operands populated from the walk's result stack.
  exprt convert_irep_to_exprt(const irept &);
  typet function_signature_declaration();
  signature_with_parameter_idst function_signature_definition();
  void check_matching_operand_types(const exprt::operandst &) const;
  exprt multi_ary(irep_idt, const exprt::operandst &);
  exprt binary_predicate(irep_idt, const exprt::operandst &);
  exprt binary(irep_idt, const exprt::operandst &);
  exprt unary(irep_idt, const exprt::operandst &);
  exprt bv_division(const exprt::operandst &, bool is_signed);
  exprt bv_mod(const exprt::operandst &, bool is_signed);

  std::pair<binding_exprt::variablest, exprt> binding(irep_idt);
  exprt lambda_expression();
  exprt let_expression();
  exprt quantifier_expression(irep_idt);
  exprt function_application(
    const symbol_exprt &function,
    const exprt::operandst &op);

  /// Apply typecast to signedbv to expressions in vector
  exprt::operandst cast_bv_to_signed(const exprt::operandst &);

  /// Apply typecast to unsignedbv to given expression
  exprt cast_bv_to_unsigned(const exprt &);

  // sorts
  typet sort();
  typet function_sort();
  std::unordered_map<std::string, std::function<typet()>> sorts;
  void setup_sorts();

  // hashtable for all commands
  std::unordered_map<std::string, std::function<void()>> commands;

  void command_sequence();
  void command(const std::string &);
  void ignore_command();
  void setup_commands();
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_PARSER_H
