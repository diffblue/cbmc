/*******************************************************************\

Module: C Defines

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// c_defines

#ifndef CPROVER_CRANGLER_C_DEFINES_H
#define CPROVER_CRANGLER_C_DEFINES_H

#include <util/optional.h>

#include <string>
#include <unordered_map>
#include <vector>

/// This class maintains a representation of one assignment to the
/// preprocessor macros in a C program.
class c_definest
{
public:
  struct definet
  {
    optionalt<std::vector<std::string>> parameters;
    std::string value;
  };

  using mapt = std::unordered_map<std::string, definet>;
  mapt map;

  void parse(const std::string &);
  std::string operator()(const std::string &) const;
};

#endif // CPROVER_CRANGLER_C_DEFINES_H
