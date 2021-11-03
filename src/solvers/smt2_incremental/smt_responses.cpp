// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_responses.h>

#include <util/range.h>

// Define the irep_idts for responses.
#define RESPONSE_ID(the_id, the_base)                                          \
  const irep_idt ID_smt_##the_id##_response{"smt_" #the_id "_response"};
#include <solvers/smt2_incremental/smt_responses.def>
#undef RESPONSE_ID

bool smt_responset::operator==(const smt_responset &other) const
{
  return irept::operator==(other);
}

bool smt_responset::operator!=(const smt_responset &other) const
{
  return !(*this == other);
}

#define RESPONSE_ID(the_id, the_base)                                          \
  template <>                                                                  \
  const smt_##the_id##_responset *the_base::cast<smt_##the_id##_responset>()   \
    const &                                                                    \
  {                                                                            \
    return id() == ID_smt_##the_id##_response                                  \
             ? static_cast<const smt_##the_id##_responset *>(this)             \
             : nullptr;                                                        \
  }
#include <solvers/smt2_incremental/smt_responses.def> // NOLINT(build/include)
#undef RESPONSE_ID

template <typename sub_classt>
const sub_classt *smt_responset::cast() const &
{
  return nullptr;
}

bool smt_check_sat_response_kindt::
operator==(const smt_check_sat_response_kindt &other) const
{
  return irept::operator==(other);
}

bool smt_check_sat_response_kindt::
operator!=(const smt_check_sat_response_kindt &other) const
{
  return !(*this == other);
}

smt_success_responset::smt_success_responset()
  : smt_responset{ID_smt_success_response}
{
}

smt_sat_responset::smt_sat_responset()
  : smt_check_sat_response_kindt{ID_smt_sat_response}
{
}

smt_unsat_responset::smt_unsat_responset()
  : smt_check_sat_response_kindt{ID_smt_unsat_response}
{
}

smt_unknown_responset::smt_unknown_responset()
  : smt_check_sat_response_kindt{ID_smt_unknown_response}
{
}

template <typename derivedt>
smt_check_sat_response_kindt::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_termt to store it.");
}

template <typename derivedt>
irept smt_check_sat_response_kindt::storert<derivedt>::upcast(
  smt_check_sat_response_kindt check_sat_response_kind)
{
  return static_cast<irept &&>(std::move(check_sat_response_kind));
}

template <typename derivedt>
const smt_check_sat_response_kindt &
smt_check_sat_response_kindt::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_check_sat_response_kindt &>(irep);
}

smt_check_sat_responset::smt_check_sat_responset(
  smt_check_sat_response_kindt kind)
  : smt_responset{ID_smt_check_sat_response}
{
  set(ID_value, upcast(std::move(kind)));
}

const smt_check_sat_response_kindt &smt_check_sat_responset::kind() const
{
  return downcast(find(ID_value));
}

smt_get_value_responset::valuation_pairt::valuation_pairt(
  smt_termt descriptor,
  smt_termt value)
{
  get_sub().push_back(upcast(std::move(descriptor)));
  get_sub().push_back(upcast(std::move(value)));
}

const smt_termt &smt_get_value_responset::valuation_pairt::descriptor() const
{
  return downcast(get_sub().at(0));
}

const smt_termt &smt_get_value_responset::valuation_pairt::value() const
{
  return downcast(get_sub().at(1));
}

bool smt_get_value_responset::valuation_pairt::
operator==(const smt_get_value_responset::valuation_pairt &other) const
{
  return irept::operator==(other);
}

bool smt_get_value_responset::valuation_pairt::
operator!=(const smt_get_value_responset::valuation_pairt &other) const
{
  return !(*this == other);
}

smt_get_value_responset::smt_get_value_responset(
  std::vector<valuation_pairt> pairs)
  : smt_responset(ID_smt_get_value_response)
{
  // SMT-LIB standard version 2.6 requires one or more pairs.
  // See page 47, figure 3.9: Command responses.
  INVARIANT(
    !pairs.empty(), "Get value response must contain one or more pairs.");
  for(auto &pair : pairs)
  {
    get_sub().push_back(std::move(pair));
  }
}

std::vector<
  std::reference_wrapper<const smt_get_value_responset::valuation_pairt>>
smt_get_value_responset::pairs() const
{
  return make_range(get_sub()).map([](const irept &pair) {
    return std::cref(static_cast<const valuation_pairt &>(pair));
  });
}

smt_unsupported_responset::smt_unsupported_responset()
  : smt_responset{ID_smt_unsupported_response}
{
}

smt_error_responset::smt_error_responset(irep_idt message)
  : smt_responset{ID_smt_error_response}
{
  set(ID_value, message);
}

const irep_idt &smt_error_responset::message() const
{
  return get(ID_value);
}
