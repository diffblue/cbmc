// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H

#include <solvers/smt2_incremental/smt_responses.h>
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
  explicit response_or_errort(smtt smt);
  explicit response_or_errort(std::string message);
  explicit response_or_errort(std::vector<std::string> messages);

  /// \brief Gets the smt response if the response is valid, or returns nullptr
  ///   otherwise.
  const smtt *get_if_valid() const;
  /// \brief Gets the error messages if the response is invalid, or returns
  ///   nullptr otherwise.
  const std::vector<std::string> *get_if_error() const;

private:
  // The below two fields could be a single `std::variant` field, if there was
  // an implementation of it available in the cbmc repository. However at the
  // time of writing we are targeting C++11, `std::variant` was introduced in
  // C++17 and we have no backported version.
  optionalt<smtt> smt;
  std::vector<std::string> messages;
};

response_or_errort<smt_responset>
validate_smt_response(const irept &parse_tree);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H
