// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H

#include <util/invariant.h>
#include <util/optional.h>

#include <string>
#include <vector>

/// Holds either a valid parsed response or response sub-tree of type \tparam
/// smtt or a collection of message strings explaining why the given input was
/// not valid.
template <class smtt>
class response_or_errort final
{
public:
  explicit response_or_errort(smtt smt) : smt{std::move(smt)}
  {
  }

  explicit response_or_errort(std::string message)
    : messages{std::move(message)}
  {
  }

  explicit response_or_errort(std::vector<std::string> messages)
    : messages{std::move(messages)}
  {
  }

  /// \brief Gets the smt response if the response is valid, or returns nullptr
  ///   otherwise.
  const smtt *get_if_valid() const
  {
    INVARIANT(
      smt.has_value() == messages.empty(),
      "The response_or_errort class must be in the valid state or error state, "
      "exclusively.");
    return smt.has_value() ? &smt.value() : nullptr;
  }

  /// \brief Gets the error messages if the response is invalid, or returns
  ///   nullptr otherwise.
  const std::vector<std::string> *get_if_error() const
  {
    INVARIANT(
      smt.has_value() == messages.empty(),
      "The response_or_errort class must be in the valid state or error state, "
      "exclusively.");
    return smt.has_value() ? nullptr : &messages;
  }

private:
  // The below two fields could be a single `std::variant` field, if there was
  // an implementation of it available in the cbmc repository. However at the
  // time of writing we are targeting C++11, `std::variant` was introduced in
  // C++17 and we have no backported version.
  optionalt<smtt> smt;
  std::vector<std::string> messages;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H
