// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>

#include <solvers/smt2_incremental/smt_terms.h>

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/type.h>

class value_expr_from_smt_factoryt : public smt_term_const_downcast_visitort
{
private:
  const typet &type_to_construct;
  optionalt<exprt> result;

  explicit value_expr_from_smt_factoryt(const typet &type_to_construct)
    : type_to_construct{type_to_construct}, result{}
  {
  }

  void visit(const smt_bool_literal_termt &bool_literal) override
  {
    INVARIANT(
      type_to_construct == bool_typet{},
      "Bool terms may only be used to construct bool typed expressions.");
    result = bool_literal.value() ? (exprt)true_exprt{} : false_exprt{};
  }

  void visit(const smt_identifier_termt &identifier_term) override
  {
    INVARIANT(
      false, "Unexpected conversion of identifier to value expression.");
  }

  void visit(const smt_bit_vector_constant_termt &bit_vector_constant) override
  {
    UNIMPLEMENTED;
  }

  void
  visit(const smt_function_application_termt &function_application) override
  {
    INVARIANT(
      false,
      "Unexpected conversion of function application to value expression.");
  }

public:
  /// \brief This function is complete the external interface to this class. All
  ///   construction of this class and construction of expressions should be
  ///   carried out via this function.
  static exprt make(const smt_termt &value_term, const typet &type_to_construct)
  {
    value_expr_from_smt_factoryt factory{type_to_construct};
    value_term.accept(factory);
    INVARIANT(factory.result.has_value(), "Factory must result in expr value.");
    return *factory.result;
  }
};

exprt construct_value_expr_from_smt(
  const smt_termt &value_term,
  const typet &type_to_construct)
{
  return value_expr_from_smt_factoryt::make(value_term, type_to_construct);
}
