/*******************************************************************\

Module: Get goto program target from location number or regex

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANALYSES_GET_TARGET_H
#define CPROVER_ANALYSES_GET_TARGET_H

#include <goto-programs/goto_functions.h>
#include <util/string2int.h>

#include <utility>

class get_targett
{
public:
  get_targett(const goto_functionst &goto_functions, const namespacet &ns)
    : goto_functions(goto_functions), ns(ns) {}

  typedef goto_programt::const_targett locationt;
  typedef std::pair<bool, locationt> rest;

  rest from_location_number(unsigned location_number);

  // if first=false, then the function only returns true (first
  // component of rest) when the regex matches exactly one location
  rest from_regex(const std::string &regex, const bool first=false);

  rest from_location_number_string(const std::string &s);

  // the specifier is either an integer string, or a regex specifier
  // (starting with "r" which is stripped off)
  rest from_spec(const std::string &spec, const bool first=false);

protected:
  const goto_functionst &goto_functions;
  const namespacet &ns;

  typedef goto_functionst::goto_functiont goto_functiont;
};

#endif
