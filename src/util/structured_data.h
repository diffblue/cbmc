/*******************************************************************\

Module: Classes for representing generic structured data

Author: Thomas Kiley

\*******************************************************************/
#ifndef CPROVER_UTIL_STRUCTURED_DATA_H
#define CPROVER_UTIL_STRUCTURED_DATA_H

#include <string>
#include <vector>

struct labelt
{
public:
  explicit labelt(std::vector<std::string> components);

  std::string camel_case() const;
  std::string snake_case() const;
  std::string kebab_case() const;
  std::string pretty() const;

  bool operator<(const labelt &other) const;

private:
  std::vector<std::string> components;
};


#endif // CPROVER_UTIL_STRUCTURED_DATA_H
