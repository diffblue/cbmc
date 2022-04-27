// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/type.h>

#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>
#include <solvers/smt2_incremental/smt_terms.h>

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
    const auto sort_width = bit_vector_constant.get_sort().bit_width();
    if(
      const auto pointer_type =
        type_try_dynamic_cast<pointer_typet>(type_to_construct))
    {
      INVARIANT(
        pointer_type->get_width() == sort_width,
        "Width of smt bit vector term must match the width of pointer type.");
      if(bit_vector_constant.value() == 0)
      {
        result = null_pointer_exprt{*pointer_type};
      }
      else
      {
        // The reason we are manually constructing a constant_exprt here is a
        // limitation in the design of `from_integer`, which only allows it to
        // be used with pointer values of 0 (null pointers).
        result = constant_exprt{
          integer2bvrep(bit_vector_constant.value(), sort_width),
          *pointer_type};
      }
      return;
    }
    if(
      const auto bitvector_type =
        type_try_dynamic_cast<bitvector_typet>(type_to_construct))
    {
      INVARIANT(
        bitvector_type->get_width() == sort_width,
        "Width of smt bit vector term must match the width of bit vector "
        "type.");
      result = from_integer(bit_vector_constant.value(), type_to_construct);
      return;
    }

    INVARIANT(
      false,
      "construct_value_expr_from_smt for bit vector should not be applied to "
      "unsupported type " +
        type_to_construct.pretty());
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
