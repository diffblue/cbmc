// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/type.h>

#include <solvers/flattening/pointer_logic.h>
#include <solvers/smt2_incremental/ast/smt_terms.h>
#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>

class value_expr_from_smt_factoryt : public smt_term_const_downcast_visitort
{
private:
  const typet &type_to_construct;
  const namespacet &ns;
  const smt_object_mapt *object_map;
  const smt_expression_identifier_mapt *expression_identifiers;
  std::optional<exprt> result;

  explicit value_expr_from_smt_factoryt(
    const typet &type_to_construct,
    const namespacet &ns,
    const smt_object_mapt *object_map = nullptr,
    const smt_expression_identifier_mapt *expression_identifiers = nullptr)
    : type_to_construct{type_to_construct},
      ns{ns},
      object_map{object_map},
      expression_identifiers{expression_identifiers},
      result{}
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
      // Special case for null pointers, where the value is zero.
      if(bit_vector_constant.value() == 0)
      {
        result = null_pointer_exprt{*pointer_type};
      }
      else if(object_map)
      {
        result = build_annotated_pointer(bit_vector_constant, *pointer_type);
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
    if(
      const auto c_enum_tag_type =
        type_try_dynamic_cast<c_enum_tag_typet>(type_to_construct))
    {
      const c_enum_typet &real_type = ns.follow_tag(*c_enum_tag_type);
      INVARIANT(
        to_bitvector_type(real_type.underlying_type()).get_width() ==
          sort_width,
        "Width of smt bit vector term must match the width of bit vector "
        "underlying type of the original c_enum type.");
      result = from_integer(bit_vector_constant.value(), real_type);
      result->type() = type_to_construct;
      return;
    }

    INVARIANT(
      false,
      "construct_value_expr_from_smt for bit vector should not be applied to "
      "unsupported type " +
        type_to_construct.pretty());
  }

  /// \brief Build an annotated pointer constant from a bit-vector value
  ///   using the object map to reconstruct the symbolic pointer expression.
  exprt build_annotated_pointer(
    const smt_bit_vector_constant_termt &bit_vector_constant,
    const pointer_typet &pointer_type)
  {
    const auto sort_width = bit_vector_constant.get_sort().bit_width();
    const irep_idt bvrep =
      integer2bvrep(bit_vector_constant.value(), sort_width);
    const std::size_t object_bits = config.bv_encoding.object_bits;
    const std::size_t pointer_width = pointer_type.get_width();
    INVARIANT(
      pointer_width > object_bits,
      "Pointer width should be wider than object bits.");
    const std::size_t offset_bits = pointer_width - object_bits;

    // Extract object ID from high bits.
    const mp_integer object_id = bit_vector_constant.value() >> offset_bits;

    // Extract offset from low bits as unsigned, matching the SAT
    // backend's interpretation in bv_pointers.cpp.
    const mp_integer offset =
      bit_vector_constant.value() % power(2, offset_bits);

    // Null object with non-zero offset represents an integer address
    // (e.g., (int *)0xDEADBEEF). Match the SAT backend's rendering in
    // pointer_logict::pointer_expr: emit `((T *)NULL) + offset` rather
    // than `(T *)<offset>` so the two backends produce identical trace
    // output.
    if(object_id == 0)
    {
      null_pointer_exprt null{pointer_type};
      return annotated_pointer_constant_exprt{
        bvrep, plus_exprt{null, from_integer(offset, pointer_diff_type())}};
    }

    // Look up object by unique_id via linear scan (object_map is
    // typically small).
    const std::size_t object_id_as_size_t =
      numeric_cast_v<std::size_t>(object_id);
    const decision_procedure_objectt *found_object = nullptr;
    for(const auto &entry : *object_map)
    {
      if(entry.second.unique_id == object_id_as_size_t)
      {
        found_object = &entry.second;
        break;
      }
    }

    if(found_object == nullptr)
    {
      // Unknown object - fall back to plain constant.
      return constant_exprt{bvrep, pointer_type};
    }

    const decision_procedure_objectt &object = *found_object;

    // Invalid pointer object.
    if(object.base_expression == make_invalid_pointer_expr())
      return annotated_pointer_constant_exprt{
        bvrep, constant_exprt("INVALID", pointer_type)};

    // Resolve the base expression through the expression_identifiers
    // reverse map. When string constants or other expressions are
    // substituted with symbol_exprt identifiers during SMT conversion,
    // the object_map tracks the substituted symbol rather than the
    // original expression. We reverse that lookup here to recover the
    // original expression for display in traces.
    //
    // TODO(perf): the linear scan below is O(M) per pointer value
    // reconstructed, where M is the number of substituted expressions.
    // For long traces with many pointer values this becomes O(N*M).
    // A dedicated reverse map (identifier -> exprt) maintained
    // alongside expression_identifiers in
    // smt2_incremental_decision_proceduret would make this O(1).
    exprt resolved_expr = object.base_expression;
    if(const auto *sym =
         expr_try_dynamic_cast<symbol_exprt>(object.base_expression);
       expression_identifiers && sym)
    {
      for(const auto &entry : *expression_identifiers)
      {
        if(entry.second.identifier() == sym->get_identifier())
        {
          resolved_expr = entry.first;
          break;
        }
      }
    }

    // Delegate the symbolic pointer construction to the shared helper
    // also used by the SAT backend's pointer_logict::pointer_expr; this
    // keeps the two trace-rendering paths in sync.
    const exprt symbolic =
      pointer_expr_for_object(resolved_expr, offset, pointer_type, ns);
    return annotated_pointer_constant_exprt{bvrep, symbolic};
  }

  void
  visit(const smt_function_application_termt &function_application) override
  {
    INVARIANT(
      false,
      "Unexpected conversion of function application to value expression.");
  }

  void visit(const smt_forall_termt &forall) override
  {
    INVARIANT(
      false, "Unexpected conversion of forall quantifier to value expression.");
  }

  void visit(const smt_exists_termt &exists) override
  {
    INVARIANT(
      false, "Unexpected conversion of exists quantifier to value expression.");
  }

public:
  /// \brief Construct an expression representing \p value_term.
  static exprt make(
    const smt_termt &value_term,
    const typet &type_to_construct,
    const namespacet &ns)
  {
    value_expr_from_smt_factoryt factory{type_to_construct, ns};
    value_term.accept(factory);
    INVARIANT(factory.result.has_value(), "Factory must result in expr value.");
    return *factory.result;
  }

  /// \brief Overload accepting an object map and expression-identifiers map
  ///   for resolving substituted expressions in pointer annotation.
  static exprt make(
    const smt_termt &value_term,
    const typet &type_to_construct,
    const namespacet &ns,
    const smt_object_mapt &object_map,
    const smt_expression_identifier_mapt &expression_identifiers)
  {
    value_expr_from_smt_factoryt factory{
      type_to_construct, ns, &object_map, &expression_identifiers};
    value_term.accept(factory);
    INVARIANT(factory.result.has_value(), "Factory must result in expr value.");
    return *factory.result;
  }
};

exprt construct_value_expr_from_smt(
  const smt_termt &value_term,
  const typet &type_to_construct,
  const namespacet &ns)
{
  return value_expr_from_smt_factoryt::make(value_term, type_to_construct, ns);
}

exprt construct_value_expr_from_smt(
  const smt_termt &value_term,
  const typet &type_to_construct,
  const namespacet &ns,
  const smt_object_mapt &object_map,
  const smt_expression_identifier_mapt &expression_identifiers)
{
  return value_expr_from_smt_factoryt::make(
    value_term, type_to_construct, ns, object_map, expression_identifiers);
}
