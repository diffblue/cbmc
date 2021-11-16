// Author: Diffblue Ltd.

#ifndef CPROVER_TESTING_UTILS_SMT2IREP_H
#define CPROVER_TESTING_UTILS_SMT2IREP_H

#include <testing-utils/use_catch.h>

#include <util/irep.h>
#include <util/optional.h>

#include <string>

struct smt2_parser_test_resultt
{
  optionalt<irept> parsed_output;
  std::string messages;
};

bool operator==(
  const smt2_parser_test_resultt &left,
  const smt2_parser_test_resultt &right);

smt2_parser_test_resultt smt2irep(const std::string &input);

class smt2_parser_error_containingt
  : public Catch::MatcherBase<smt2_parser_test_resultt>
{
public:
  explicit smt2_parser_error_containingt(std::string expected_error);
  bool match(const smt2_parser_test_resultt &exception) const override;
  std::string describe() const override;

private:
  std::string expected_error;
};

smt2_parser_test_resultt smt2_parser_success(irept parse_tree);

#endif // CPROVER_TESTING_UTILS_SMT2IREP_H
