// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_bit_vector_theory.h>

#include <util/invariant.h>

const char *smt_bit_vector_theoryt::concatt::identifier()
{
  return "concat";
}

smt_sortt smt_bit_vector_theoryt::concatt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  const auto get_width = [](const smt_termt &term) {
    return term.get_sort().cast<smt_bit_vector_sortt>()->bit_width();
  };
  return smt_bit_vector_sortt{get_width(lhs) + get_width(rhs)};
}

static void validate_bit_vector_sort(
  const std::string &descriptor,
  const smt_termt &operand)
{
  const auto operand_sort = operand.get_sort().cast<smt_bit_vector_sortt>();
  INVARIANT(
    operand_sort,
    descriptor + " operand is expected to have a bit-vector sort.");
}

static void validate_bit_vector_sort(const smt_termt &operand)
{
  validate_bit_vector_sort("The", operand);
}

static void
validate_bit_vector_sorts(const smt_termt &lhs, const smt_termt &rhs)
{
  validate_bit_vector_sort("Left", lhs);
  validate_bit_vector_sort("Right", rhs);
}

void smt_bit_vector_theoryt::concatt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::concatt>
  smt_bit_vector_theoryt::concat{};

const char *smt_bit_vector_theoryt::extractt::identifier()
{
  return "extract";
}

smt_sortt
smt_bit_vector_theoryt::extractt::return_sort(const smt_termt &operand) const
{
  return smt_bit_vector_sortt{i - j + 1};
}

std::vector<smt_indext> smt_bit_vector_theoryt::extractt::indices() const
{
  return {smt_numeral_indext{i}, smt_numeral_indext{j}};
}

void smt_bit_vector_theoryt::extractt::validate(const smt_termt &operand) const
{
  PRECONDITION(i >= j);
  const auto bit_vector_sort = operand.get_sort().cast<smt_bit_vector_sortt>();
  PRECONDITION(bit_vector_sort);
  PRECONDITION(i < bit_vector_sort->bit_width());
}

smt_function_application_termt::factoryt<smt_bit_vector_theoryt::extractt>
smt_bit_vector_theoryt::extract(std::size_t i, std::size_t j)
{
  PRECONDITION(i >= j);
  return smt_function_application_termt::factoryt<extractt>(i, j);
}

static void
validate_matched_bit_vector_sorts(const smt_termt &left, const smt_termt &right)
{
  validate_bit_vector_sorts(left, right);
  // The below invariant is based on the smtlib standard.
  // See http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
  INVARIANT(
    left.get_sort() == right.get_sort(),
    "Left and right operands must have the same bit width.");
}

// Bitwise operator definitions

const char *smt_bit_vector_theoryt::nott::identifier()
{
  return "bvnot";
}

smt_sortt smt_bit_vector_theoryt::nott::return_sort(const smt_termt &operand)
{
  return operand.get_sort();
}

void smt_bit_vector_theoryt::nott::validate(const smt_termt &operand)
{
  validate_bit_vector_sort(operand);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::nott>
  smt_bit_vector_theoryt::make_not{};

const char *smt_bit_vector_theoryt::andt::identifier()
{
  return "bvand";
}

smt_sortt smt_bit_vector_theoryt::andt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::andt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::andt>
  smt_bit_vector_theoryt::make_and{};

const char *smt_bit_vector_theoryt::ort::identifier()
{
  return "bvor";
}

smt_sortt smt_bit_vector_theoryt::ort::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::ort::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::ort>
  smt_bit_vector_theoryt::make_or{};

const char *smt_bit_vector_theoryt::nandt::identifier()
{
  return "bvnand";
}

smt_sortt smt_bit_vector_theoryt::nandt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::nandt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::nandt>
  smt_bit_vector_theoryt::nand{};

const char *smt_bit_vector_theoryt::nort::identifier()
{
  return "bvnor";
}

smt_sortt smt_bit_vector_theoryt::nort::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::nort::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::nort>
  smt_bit_vector_theoryt::nor{};

const char *smt_bit_vector_theoryt::xort::identifier()
{
  return "bvxor";
}

smt_sortt smt_bit_vector_theoryt::xort::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::xort::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::xort>
  smt_bit_vector_theoryt::make_xor{};

const char *smt_bit_vector_theoryt::xnort::identifier()
{
  return "bvxnor";
}

smt_sortt smt_bit_vector_theoryt::xnort::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::xnort::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::xnort>
  smt_bit_vector_theoryt::xnor{};

const char *smt_bit_vector_theoryt::comparet::identifier()
{
  return "bvcomp";
}

smt_sortt smt_bit_vector_theoryt::comparet::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bit_vector_sortt{1};
}

void smt_bit_vector_theoryt::comparet::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::comparet>
  smt_bit_vector_theoryt::compare{};

// Relational operator definitions

const char *smt_bit_vector_theoryt::unsigned_less_thant::identifier()
{
  return "bvult";
}

smt_sortt smt_bit_vector_theoryt::unsigned_less_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_less_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_less_thant>
  smt_bit_vector_theoryt::unsigned_less_than{};

const char *smt_bit_vector_theoryt::unsigned_less_than_or_equalt::identifier()
{
  return "bvule";
}

smt_sortt smt_bit_vector_theoryt::unsigned_less_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_less_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_less_than_or_equalt>
  smt_bit_vector_theoryt::unsigned_less_than_or_equal{};

const char *smt_bit_vector_theoryt::unsigned_greater_thant::identifier()
{
  return "bvugt";
}

smt_sortt smt_bit_vector_theoryt::unsigned_greater_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_greater_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_greater_thant>
  smt_bit_vector_theoryt::unsigned_greater_than{};

const char *
smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::identifier()
{
  return "bvuge";
}

smt_sortt smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::unsigned_greater_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_greater_than_or_equalt>
  smt_bit_vector_theoryt::unsigned_greater_than_or_equal{};

const char *smt_bit_vector_theoryt::signed_less_thant::identifier()
{
  return "bvslt";
}

smt_sortt smt_bit_vector_theoryt::signed_less_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_less_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_less_thant>
  smt_bit_vector_theoryt::signed_less_than{};

const char *smt_bit_vector_theoryt::signed_less_than_or_equalt::identifier()
{
  return "bvsle";
}

smt_sortt smt_bit_vector_theoryt::signed_less_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_less_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_less_than_or_equalt>
  smt_bit_vector_theoryt::signed_less_than_or_equal{};

const char *smt_bit_vector_theoryt::signed_greater_thant::identifier()
{
  return "bvsgt";
}

smt_sortt smt_bit_vector_theoryt::signed_greater_thant::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_greater_thant::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_greater_thant>
  smt_bit_vector_theoryt::signed_greater_than{};

const char *smt_bit_vector_theoryt::signed_greater_than_or_equalt::identifier()
{
  return "bvsge";
}

smt_sortt smt_bit_vector_theoryt::signed_greater_than_or_equalt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return smt_bool_sortt{};
}

void smt_bit_vector_theoryt::signed_greater_than_or_equalt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_greater_than_or_equalt>
  smt_bit_vector_theoryt::signed_greater_than_or_equal{};

const char *smt_bit_vector_theoryt::addt::identifier()
{
  return "bvadd";
}

smt_sortt smt_bit_vector_theoryt::addt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::addt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::addt>
  smt_bit_vector_theoryt::add{};

const char *smt_bit_vector_theoryt::subtractt::identifier()
{
  return "bvsub";
}

smt_sortt smt_bit_vector_theoryt::subtractt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::subtractt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::subtractt>
  smt_bit_vector_theoryt::subtract{};

const char *smt_bit_vector_theoryt::multiplyt::identifier()
{
  return "bvmul";
}

smt_sortt smt_bit_vector_theoryt::multiplyt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::multiplyt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::multiplyt>
  smt_bit_vector_theoryt::multiply{};

const char *smt_bit_vector_theoryt::unsigned_dividet::identifier()
{
  return "bvudiv";
}

smt_sortt smt_bit_vector_theoryt::unsigned_dividet::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::unsigned_dividet::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_dividet>
  smt_bit_vector_theoryt::unsigned_divide{};

const char *smt_bit_vector_theoryt::signed_dividet::identifier()
{
  return "bvsdiv";
}

smt_sortt smt_bit_vector_theoryt::signed_dividet::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::signed_dividet::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_dividet>
  smt_bit_vector_theoryt::signed_divide{};

const char *smt_bit_vector_theoryt::unsigned_remaindert::identifier()
{
  return "bvurem";
}

smt_sortt smt_bit_vector_theoryt::unsigned_remaindert::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::unsigned_remaindert::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::unsigned_remaindert>
  smt_bit_vector_theoryt::unsigned_remainder{};

const char *smt_bit_vector_theoryt::signed_remaindert::identifier()
{
  return "bvsrem";
}

smt_sortt smt_bit_vector_theoryt::signed_remaindert::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::signed_remaindert::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::signed_remaindert>
  smt_bit_vector_theoryt::signed_remainder{};

const char *smt_bit_vector_theoryt::negatet::identifier()
{
  return "bvneg";
}

smt_sortt smt_bit_vector_theoryt::negatet::return_sort(const smt_termt &operand)
{
  return operand.get_sort();
}

void smt_bit_vector_theoryt::negatet::validate(const smt_termt &operand)
{
  validate_bit_vector_sort(operand);
}

const smt_function_application_termt::factoryt<smt_bit_vector_theoryt::negatet>
  smt_bit_vector_theoryt::negate{};

const char *smt_bit_vector_theoryt::shift_leftt::identifier()
{
  return "bvshl";
}

smt_sortt smt_bit_vector_theoryt::shift_leftt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::shift_leftt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::shift_leftt>
  smt_bit_vector_theoryt::shift_left{};

const char *smt_bit_vector_theoryt::logical_shift_rightt::identifier()
{
  return "bvlshr";
}

smt_sortt smt_bit_vector_theoryt::logical_shift_rightt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::logical_shift_rightt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::logical_shift_rightt>
  smt_bit_vector_theoryt::logical_shift_right{};

const char *smt_bit_vector_theoryt::arithmetic_shift_rightt::identifier()
{
  return "bvashr";
}

smt_sortt smt_bit_vector_theoryt::arithmetic_shift_rightt::return_sort(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  return lhs.get_sort();
}

void smt_bit_vector_theoryt::arithmetic_shift_rightt::validate(
  const smt_termt &lhs,
  const smt_termt &rhs)
{
  validate_matched_bit_vector_sorts(lhs, rhs);
}

const smt_function_application_termt::factoryt<
  smt_bit_vector_theoryt::arithmetic_shift_rightt>
  smt_bit_vector_theoryt::arithmetic_shift_right{};

const char *smt_bit_vector_theoryt::repeatt::identifier()
{
  return "repeat";
}

smt_sortt
smt_bit_vector_theoryt::repeatt::return_sort(const smt_termt &operand) const
{
  const std::size_t operand_width =
    operand.get_sort().cast<smt_bit_vector_sortt>()->bit_width();
  return smt_bit_vector_sortt{i * operand_width};
}

std::vector<smt_indext> smt_bit_vector_theoryt::repeatt::indices() const
{
  return {smt_numeral_indext{i}};
}

void smt_bit_vector_theoryt::repeatt::validate(const smt_termt &operand) const
{
  PRECONDITION(i >= 1);
  PRECONDITION(operand.get_sort().cast<smt_bit_vector_sortt>());
}

smt_function_application_termt::factoryt<smt_bit_vector_theoryt::repeatt>
smt_bit_vector_theoryt::repeat(std::size_t i)
{
  PRECONDITION(i >= 1);
  return smt_function_application_termt::factoryt<repeatt>(i);
}

const char *smt_bit_vector_theoryt::zero_extendt::identifier()
{
  return "zero_extend";
}

smt_sortt smt_bit_vector_theoryt::zero_extendt::return_sort(
  const smt_termt &operand) const
{
  const std::size_t operand_width =
    operand.get_sort().cast<smt_bit_vector_sortt>()->bit_width();
  return smt_bit_vector_sortt{i + operand_width};
}

std::vector<smt_indext> smt_bit_vector_theoryt::zero_extendt::indices() const
{
  return {smt_numeral_indext{i}};
}

void smt_bit_vector_theoryt::zero_extendt::validate(const smt_termt &operand)
{
  PRECONDITION(operand.get_sort().cast<smt_bit_vector_sortt>());
}

smt_function_application_termt::factoryt<smt_bit_vector_theoryt::zero_extendt>
smt_bit_vector_theoryt::zero_extend(std::size_t i)
{
  return smt_function_application_termt::factoryt<zero_extendt>(i);
}

const char *smt_bit_vector_theoryt::sign_extendt::identifier()
{
  return "sign_extend";
}

smt_sortt smt_bit_vector_theoryt::sign_extendt::return_sort(
  const smt_termt &operand) const
{
  const std::size_t operand_width =
    operand.get_sort().cast<smt_bit_vector_sortt>()->bit_width();
  return smt_bit_vector_sortt{i + operand_width};
}

std::vector<smt_indext> smt_bit_vector_theoryt::sign_extendt::indices() const
{
  return {smt_numeral_indext{i}};
}

void smt_bit_vector_theoryt::sign_extendt::validate(const smt_termt &operand)
{
  PRECONDITION(operand.get_sort().cast<smt_bit_vector_sortt>());
}

smt_function_application_termt::factoryt<smt_bit_vector_theoryt::sign_extendt>
smt_bit_vector_theoryt::sign_extend(std::size_t i)
{
  return smt_function_application_termt::factoryt<sign_extendt>(i);
}
