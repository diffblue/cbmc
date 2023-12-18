// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H

#include <util/invariant.h>

#include <string>
#include <variant>
#include <vector>

/// Holds either a valid parsed response or response sub-tree of type \tparam
/// smtt or a collection of message strings explaining why the given input was
/// not valid.
template <class smtt>
class response_or_errort final
{
public:
  explicit response_or_errort(smtt smt) : smt_or_messages{std::move(smt)}
  {
  }

  explicit response_or_errort(std::vector<std::string> messages)
    : smt_or_messages{std::move(messages)}
  {
  }

  /// \brief Gets the smt response if the response is valid, or returns nullptr
  ///   otherwise.
  const smtt *get_if_valid() const
  {
    return std::get_if<smtt>(&smt_or_messages);
  }

  /// \brief Gets the error messages if the response is invalid, or returns
  ///   nullptr otherwise.
  const std::vector<std::string> *get_if_error() const
  {
    return std::get_if<std::vector<std::string>>(&smt_or_messages);
  }

private:
  std::variant<smtt, std::vector<std::string>> smt_or_messages;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_RESPONSE_OR_ERROR_H
