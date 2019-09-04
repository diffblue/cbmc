/// Author: Diffblue Ltd.

#ifndef CPROVER_TESTING_UTILS_INVARIANT_H
#define CPROVER_TESTING_UTILS_INVARIANT_H

#include <testing-utils/use_catch.h>
#include <util/invariant.h>

#include <string>

class invariant_failure_containingt
  : public Catch::MatcherBase<invariant_failedt>
{
public:
  explicit invariant_failure_containingt(std::string expected);
  bool match(const invariant_failedt &exception) const override;
  std::string describe() const override;

private:
  std::string expected;
};

/// Returns a matcher which matches an invariant_failedt exception, where the
/// `.what()` returns a string containing \p expected.
invariant_failure_containingt
invariant_failure_containing(std::string expected);

/// Printing of `invariant_failedt` for test failure messages.
std::ostream &
operator<<(std::ostream &out, const invariant_failedt &invariant_failed);

#endif // CPROVER_TESTING_UTILS_INVARIANT_H
