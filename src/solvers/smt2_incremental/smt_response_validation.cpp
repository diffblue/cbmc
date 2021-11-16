// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_response_validation.h>

template <class smtt>
response_or_errort<smtt>::response_or_errort(smtt smt) : smt{std::move(smt)}
{
}

template <class smtt>
response_or_errort<smtt>::response_or_errort(std::string message)
  : messages{std::move(message)}
{
}

template <class smtt>
const smtt *response_or_errort<smtt>::get_if_valid() const
{
  INVARIANT(
    smt.has_value() == messages.empty(),
    "The response_or_errort class must be in the valid state or error state, "
    "exclusively.");
  return smt.has_value() ? &smt.value() : nullptr;
}

template <class smtt>
const std::vector<std::string> *response_or_errort<smtt>::get_if_error() const
{
  INVARIANT(
    smt.has_value() == messages.empty(),
    "The response_or_errort class must be in the valid state or error state, "
    "exclusively.");
  return smt.has_value() ? nullptr : &messages;
}

template class response_or_errort<smt_responset>;

response_or_errort<smt_responset> validate_smt_response(const irept &parse_tree)
{
  if(parse_tree.id() == "sat")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_sat_responset{}}};
  if(parse_tree.id() == "unsat")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_unsat_responset{}}};
  if(parse_tree.id() == "unknown")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_unknown_responset{}}};
  if(parse_tree.id() == "success")
    return response_or_errort<smt_responset>{smt_success_responset{}};
  UNIMPLEMENTED;
}
