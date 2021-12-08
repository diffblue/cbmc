// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>

#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>

#include <testing-utils/invariant.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <string>

static mp_integer power2(unsigned exponent)
{
  mp_integer result;
  result.setPower2(exponent);
  return result;
}

/// Returns the maximum integer value which can be stored in \p bits as an
/// unsigned integer.
static mp_integer max_int(const std::size_t bits)
{
  return power2(bits) - 1;
}

TEST_CASE("Value expr construction from smt.", "[core][smt2_incremental]")
{
  optionalt<smt_termt> input_term;
  optionalt<exprt> expected_result;

  using rowt = std::pair<smt_termt, exprt>;

  // clang-format off
#define UNSIGNED_BIT_VECTOR_TESTS(bits)                                        \
  rowt{smt_bit_vector_constant_termt{0, (bits)},                               \
       from_integer(0, unsignedbv_typet{(bits)})},                             \
  rowt{smt_bit_vector_constant_termt{42, (bits)},                              \
       from_integer(42, unsignedbv_typet{(bits)})},                            \
  rowt{smt_bit_vector_constant_termt{max_int((bits) - 1), (bits)},             \
       from_integer(max_int((bits) - 1), unsignedbv_typet{(bits)})},           \
  rowt{smt_bit_vector_constant_termt{power2((bits) - 1), (bits)},              \
       from_integer(power2((bits) - 1), unsignedbv_typet{(bits)})},            \
  rowt{smt_bit_vector_constant_termt{max_int((bits)), (bits)},                 \
       from_integer(max_int((bits)), unsignedbv_typet{(bits)})}

#define SIGNED_BIT_VECTOR_TESTS(bits)                                          \
  rowt{smt_bit_vector_constant_termt{0, (bits)},                               \
       from_integer(0, signedbv_typet{(bits)})},                               \
  rowt{smt_bit_vector_constant_termt{42, (bits)},                              \
       from_integer(42, signedbv_typet{(bits)})},                              \
  rowt{smt_bit_vector_constant_termt{max_int((bits) - 1), (bits)},             \
       from_integer(max_int((bits) - 1), signedbv_typet{(bits)})},             \
  rowt{smt_bit_vector_constant_termt{power2((bits) - 1), (bits)},              \
       from_integer(-power2((bits) - 1), signedbv_typet{(bits)})},             \
  rowt{smt_bit_vector_constant_termt{max_int((bits)), (bits)},                 \
       from_integer(-1, signedbv_typet{(bits)})}
  // clang-format on

  std::tie(input_term, expected_result) = GENERATE(
    rowt{smt_bool_literal_termt{true}, true_exprt{}},
    rowt{smt_bool_literal_termt{false}, false_exprt{}},
    UNSIGNED_BIT_VECTOR_TESTS(8),
    SIGNED_BIT_VECTOR_TESTS(8),
    UNSIGNED_BIT_VECTOR_TESTS(16),
    SIGNED_BIT_VECTOR_TESTS(16),
    UNSIGNED_BIT_VECTOR_TESTS(32),
    SIGNED_BIT_VECTOR_TESTS(32),
    UNSIGNED_BIT_VECTOR_TESTS(64),
    SIGNED_BIT_VECTOR_TESTS(64));
  SECTION(
    "Construction of \"" + id2string(expected_result->type().id()) +
    "\" from \"" + smt_to_smt2_string(*input_term) + "\"")
  {
    REQUIRE(
      construct_value_expr_from_smt(*input_term, expected_result->type()) ==
      *expected_result);
  }
}

TEST_CASE(
  "Invariant violations in value expr construction from smt.",
  "[core][smt2_incremental]")
{
  optionalt<smt_termt> input_term;
  optionalt<typet> input_type;
  std::string invariant_reason;

  using rowt = std::tuple<smt_termt, typet, std::string>;
  std::tie(input_term, input_type, invariant_reason) = GENERATE(
    rowt{smt_bool_literal_termt{true},
         unsignedbv_typet{16},
         "Bool terms may only be used to construct bool typed expressions."},
    rowt{smt_identifier_termt{"foo", smt_bit_vector_sortt{16}},
         unsignedbv_typet{16},
         "Unexpected conversion of identifier to value expression."},
    rowt{
      smt_bit_vector_constant_termt{0, 8},
      unsignedbv_typet{16},
      "Width of smt bit vector term must match the width of bit vector type."},
    rowt{smt_bit_vector_constant_termt{0, 8},
         empty_typet{},
         "construct_value_expr_from_smt for bit vector should not be applied "
         "to unsupported type empty"},
    rowt{smt_core_theoryt::make_not(smt_bool_literal_termt{true}),
         unsignedbv_typet{16},
         "Unexpected conversion of function application to value expression."});
  SECTION(invariant_reason)
  {
    const cbmc_invariants_should_throwt invariants_throw;
    REQUIRE_THROWS_MATCHES(
      construct_value_expr_from_smt(*input_term, *input_type),
      invariant_failedt,
      invariant_failure_containing(invariant_reason));
  }
}
