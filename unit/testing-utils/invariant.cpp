/// Author: Diffblue Ltd.

#include "invariant.h"

#include <utility>

invariant_failure_containingt invariant_failure_containing(std::string expected)
{
  return invariant_failure_containingt{std::move(expected)};
}

invariant_failure_containingt::invariant_failure_containingt(
  std::string expected)
  : expected{std::move(expected)}
{
}

bool invariant_failure_containingt::match(
  const invariant_failedt &exception) const
{
  const std::string what = exception.what();
  return what.find(expected) != std::string::npos;
}

std::string invariant_failure_containingt::describe() const
{
  return std::string{"invariant_failedt with `.what' containing - \""} +
         expected + "\"";
}

std::ostream &
operator<<(std::ostream &out, const invariant_failedt &invariant_failed)
{
  out << "invariant_failedt where `.what()' is \"" << invariant_failed.what()
      << "\"";
  return out;
}
