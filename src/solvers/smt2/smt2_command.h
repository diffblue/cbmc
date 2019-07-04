/*******************************************************************\

Module: SMT2 solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// SMT2 commands

#ifndef CPROVER_SOLVERS_SMT2_SMT2_COMMAND_H
#define CPROVER_SOLVERS_SMT2_SMT2_COMMAND_H

#include "smt2_ast.h"

class smt2_command_or_commentt
{
public:
  virtual void print(std::ostream &stream) const = 0;
  virtual ~smt2_command_or_commentt() = default;
};

inline std::ostream &
operator<<(std::ostream &stream, const smt2_command_or_commentt &command)
{
  command.print(stream);
  return stream;
}

/// See the SMT-LIB standard for explanations about the meaning of the commands:
/// http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r10.12.21.pdf
class smt2_commandt final : public smt2_command_or_commentt
{
public:
  void print(std::ostream &stream) const override;

  static smt2_commandt set_logic(smt2_symbolt symbol)
  {
    return smt2_commandt{"set-logic", {std::move(symbol)}};
  }

  static smt2_commandt declare_fun(
    smt2_symbolt symbol,
    smt2_listt<smt2_sortt> arguments,
    smt2_sortt result)
  {
    return smt2_commandt{
      "declare-fun",
      {std::move(symbol), std::move(arguments), std::move(result)}};
  }

  static smt2_commandt define_fun(
    smt2_symbolt symbol,
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>> arguments,
    smt2_sortt result_sort,
    smt2_astt result_expr)
  {
    return smt2_commandt{"define-fun",
                         {std::move(symbol),
                          std::move(arguments),
                          std::move(result_sort),
                          std::move(result_expr)}};
  }

  static smt2_commandt declare_sort(smt2_symbolt symbol, smt2_constantt numeral)
  {
    return smt2_commandt{"declare-sort",
                         {std::move(symbol), std::move(numeral)}};
  }

  static smt2_commandt define_sort(
    smt2_symbolt symbol,
    smt2_listt<smt2_symbolt> arguments,
    smt2_astt expr)
  {
    return smt2_commandt{
      "define-sort",
      {std::move(symbol), std::move(arguments), std::move(expr)}};
  }

  static smt2_commandt _assert(smt2_astt expr)
  {
    return smt2_commandt{"assert", {std::move(expr)}};
  }

  static smt2_commandt get_assertions()
  {
    return smt2_commandt{"get-assertions", {}};
  }

  static smt2_commandt check_sat()
  {
    return smt2_commandt{"check-sat", {}};
  }

  static smt2_commandt get_proof()
  {
    return smt2_commandt{"get-proof", {}};
  }

  static smt2_commandt get_unsat_core()
  {
    return smt2_commandt{"get-unsat-core", {}};
  }

  static smt2_commandt get_value(smt2_listt<smt2_astt> terms)
  {
    return smt2_commandt{"get-value", {std::move(terms)}};
  }

  static smt2_commandt get_assignment()
  {
    return smt2_commandt{"get-assignment", {}};
  }

  static smt2_commandt push(smt2_constantt numeral)
  {
    return smt2_commandt{"push", {std::move(numeral)}};
  }

  static smt2_commandt pop(smt2_constantt numeral)
  {
    return smt2_commandt{"pop", {std::move(numeral)}};
  }

  static smt2_commandt get_option(smt2_symbolt keyword)
  {
    return smt2_commandt{"get-option", {std::move(keyword)}};
  }

  static smt2_commandt set_option(smt2_symbolt keyword, smt2_astt value)
  {
    return smt2_commandt{"set-option", {std::move(keyword), std::move(value)}};
  }

  static smt2_commandt get_info(smt2_symbolt keyword)
  {
    return smt2_commandt{"get-info", {std::move(keyword)}};
  }

  static smt2_commandt set_info(smt2_symbolt keyword, smt2_astt value)
  {
    return smt2_commandt{"set-info", {std::move(keyword), std::move(value)}};
  }

  static smt2_commandt exit()
  {
    return smt2_commandt{"exit", {}};
  }

  static smt2_commandt declare_datatypes(
    smt2_listt<smt2_sort_declarationt> sort_decs,
    smt2_listt<smt2_datatype_declarationt> datatype_decs)
  {
    return smt2_commandt{"declare-datatypes",
                         {std::move(sort_decs), std::move(datatype_decs)}};
  }

  static smt2_commandt
  declare_datatypes(smt2_listt<smt2_datatype_declarationt> datatype_decs)
  {
    return declare_datatypes(
      smt2_listt<smt2_sort_declarationt>{{}}, std::move(datatype_decs));
  }

private:
  irep_idt name;
  std::vector<smt2_astt> arguments;

  smt2_commandt(irep_idt name, std::vector<smt2_astt> arguments)
    : name(std::move(name)), arguments(std::move(arguments))
  {
  }
};

void smt2_commandt::print(std::ostream &stream) const
{
  stream << '(' << name;
  for(const auto &arg : arguments)
    stream << ' ' << arg;
  stream << ")\n";
}

class smt2_commentt final : public smt2_command_or_commentt
{
public:
  void print(std::ostream &stream) const override
  {
    stream << "; " << content << '\n';
  }

  explicit smt2_commentt(std::string content) : content(std::move(content))
  {
  }

private:
  std::string content;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_COMMAND_H
